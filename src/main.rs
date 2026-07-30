#![windows_subsystem = "windows"]
use eframe::{egui, App, Frame};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicIsize, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};
use rdev::{listen, EventType, Key};
use std::collections::HashMap;
use parking_lot::Mutex;
use windows::Win32::UI::Input::KeyboardAndMouse::{
    INPUT, INPUT_0, MOUSEINPUT, INPUT_MOUSE, SendInput, GetActiveWindow,
    MOUSEEVENTF_LEFTDOWN, MOUSEEVENTF_LEFTUP,
    KEYBDINPUT, INPUT_KEYBOARD, KEYEVENTF_KEYUP, VIRTUAL_KEY,
};
use windows::Win32::UI::WindowsAndMessaging::{
    GetForegroundWindow,
};
// --- Constants ---
const MAX_MACROS: usize = 50;
const FEEDBACK_DURATION: Duration = Duration::from_secs(2);

// Default VK codes
const DEFAULT_AUTOCLICKER_KEY: u32 = 0x75; // F6
const DEFAULT_MASTER_SWITCH_KEY: u32 = 0x76; // F7

// --- Macro Key Press Info ---
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MacroKeyPress {
    vk_code: u32,
}

// --- Macro Button State ---
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MacroButtonState {
    Idle,
    WaitingKey,
    Running,
}

// --- Macro Definition ---
#[derive(Debug, Clone)]
struct Macro {
    id: u32,
    /// Seconds between each key press.
    repeat_interval: f32,
    repeat_count: u32,
    repetition_count: u32,
    state: MacroButtonState,
    recorded_key: Option<MacroKeyPress>,
}

impl Default for Macro {
    fn default() -> Self {
        Self {
            id: 0,
            repeat_interval: 0.1, // 10 CPS default
            repeat_count: 0,
            repetition_count: 0,
            state: MacroButtonState::Idle,
            recorded_key: None,
        }
    }
}

/// # Lock ordering
///
/// When both `macros` and `free_ids` must be locked, always acquire `macros`
/// first, then `free_ids`. Both `add_macro` and `remove_macro` follow this
/// order. Violating it risks deadlock.
struct SharedState {
    /// Whether the autoclicker is currently running.
    is_running: AtomicBool,
    /// Global shutdown flag (set on app exit).
    shutdown: AtomicBool,
    /// 0 = CPS mode, 1 = Slow mode.
    mode: AtomicU32,
    /// CPS value stored as f32 bits.
    cps_value: AtomicU32,
    /// Slow mode interval stored as f32 bits (seconds).
    slow_value: AtomicU32,
    /// Next macro ID to assign (monotonically increasing).
    next_macro_id: AtomicU32,
    /// IDs that were freed by removing macros, to be reused.
    free_ids: Arc<Mutex<Vec<u32>>>,
    /// All macros keyed by ID.
    macros: Arc<Mutex<HashMap<u32, Macro>>>,
    /// Index of the currently selected macro (0 = none selected).
    current_macro_id: AtomicU32,
    /// Whether macros are allowed to run (toggled by master switch). Starts OFF —
    /// recording a key only arms a macro, it never fires until the master
    /// switch hotkey is pressed.
    macros_enabled: AtomicBool,
    /// Configurable key for autoclicker toggle.
    autoclicker_key: AtomicU32,
    /// Configurable key for master macro switch.
    master_switch_key: AtomicU32,
    /// Tracks if the app is waiting for a key press to rebind a setting.
    /// 0: Not waiting, 1: Waiting for autoclicker key, 2: Waiting for master switch key.
    rebinding_target: AtomicU32,
    /// Failsafe: when enabled, if the app window loses focus, autoclicker and macros auto-stop.
    failsafe_enabled: AtomicBool,
    /// The HWND (handle) of our app window, stored as isize for atomic operations.
    target_hwnd: AtomicIsize,
    /// Cached focus flag — updated by GUI thread, read-only by workers.
    window_focused: AtomicBool,
}

impl SharedState {
    fn new() -> Self {
        Self {
            is_running: AtomicBool::new(false),
            shutdown: AtomicBool::new(false),
            mode: AtomicU32::new(0),
            cps_value: AtomicU32::new(1.0f32.to_bits()),
            slow_value: AtomicU32::new(10.0f32.to_bits()),
            next_macro_id: AtomicU32::new(1),
            free_ids: Arc::new(Mutex::new(Vec::new())),
            macros: Arc::new(Mutex::new(HashMap::new())),
            current_macro_id: AtomicU32::new(0),
            macros_enabled: AtomicBool::new(false),
            autoclicker_key: AtomicU32::new(DEFAULT_AUTOCLICKER_KEY),
            master_switch_key: AtomicU32::new(DEFAULT_MASTER_SWITCH_KEY),
            rebinding_target: AtomicU32::new(0),
            failsafe_enabled: AtomicBool::new(true),
            target_hwnd: AtomicIsize::new(0),
            window_focused: AtomicBool::new(true),
        }
    }

    /// Check failsafe — called by GUI thread once per frame.
    ///
    /// This is intentionally EDGE-triggered: it only stops the clicker/macros
    /// the moment the window goes from focused -> unfocused (e.g. you alt-tab,
    /// hit Win+D, or Ctrl+Alt+Del away while it's running). It must NOT keep
    /// forcing things off every frame just because the window currently lacks
    /// focus — that would defeat the entire point of the global toggle hotkeys,
    /// which are meant to start/stop the clicker while some other window
    /// (e.g. a game) is in the foreground.
    fn update_failsafe_from_gui(&self) {
        let hwnd = self.target_hwnd.load(Ordering::Relaxed);
        if hwnd == 0 {
            return;
        }
        let focused = unsafe {
            let foreground = GetForegroundWindow();
            (foreground.0 as isize) == hwnd
        };
        let was_focused = self.window_focused.swap(focused, Ordering::Relaxed);

        if !self.failsafe_enabled.load(Ordering::Relaxed) {
            return;
        }

        // Only react to a focused -> unfocused transition, not the steady state.
        if was_focused && !focused {
            self.is_running.store(false, Ordering::Relaxed);
            self.macros_enabled.store(false, Ordering::Relaxed);
        }
    }

    fn add_macro(&self) -> u32 {
        let mut macros = self.macros.lock();
        if macros.len() >= MAX_MACROS {
            return 0;
        }
        // Reuse a freed ID if available, otherwise allocate a new one
        let id = {
            let mut free = self.free_ids.lock();
            free.pop().unwrap_or_else(|| self.next_macro_id.fetch_add(1, Ordering::Relaxed))
        };
        let mut new_macro = Macro::default();
        new_macro.id = id;
        macros.insert(id, new_macro);
        id
    }

    fn remove_macro(&self, id: u32) -> bool {
        if id == 0 {
            return false;
        }
        let mut macros = self.macros.lock();
        if macros.remove(&id).is_some() {
            let mut free = self.free_ids.lock();
            free.push(id);
            true
        } else {
            false
        }
    }

    /// Return a sorted snapshot of all macros by ID.
    fn snapshot_sorted(&self) -> Vec<Macro> {
        let mut vec = self.snapshot();
        vec.sort_by_key(|m| m.id);
        vec
    }

    fn get_macro(&self, id: u32) -> Option<Macro> {
        let macros = self.macros.lock();
        macros.get(&id).cloned()
    }

    /// Atomically modify a macro via closure — avoids extra clone + write round-trips.
    fn modify_macro<F>(&self, id: u32, f: F)
    where
        F: FnOnce(&mut Macro),
    {
        let mut macros = self.macros.lock();
        if let Some(existing) = macros.get_mut(&id) {
            f(existing);
        }
    }

    /// Lock once and clone all macros — avoids N+1 mutex acquisitions per frame
    /// when iterating over all macros in the UI.
    fn snapshot(&self) -> Vec<Macro> {
        let macros = self.macros.lock();
        macros.values().cloned().collect()
    }

    fn macro_count(&self) -> usize {
        self.macros.lock().len()
    }

    fn get_current_macro_id(&self) -> u32 {
        self.current_macro_id.load(Ordering::Relaxed)
    }

    fn set_current_macro_id(&self, index: u32) {
        self.current_macro_id.store(index, Ordering::Relaxed);
    }

    fn key_to_vk_code(key: &Key) -> u32 {
        match key {
            Key::Num0 => 0x30, Key::Num1 => 0x31, Key::Num2 => 0x32,
            Key::Num3 => 0x33, Key::Num4 => 0x34, Key::Num5 => 0x35,
            Key::Num6 => 0x36, Key::Num7 => 0x37, Key::Num8 => 0x38,
            Key::Num9 => 0x39,
            Key::F1 => 0x70, Key::F2 => 0x71, Key::F3 => 0x72,
            Key::F4 => 0x73, Key::F5 => 0x74, Key::F6 => 0x75,
            Key::F7 => 0x76, Key::F8 => 0x77, Key::F9 => 0x78,
            Key::F10 => 0x79, Key::F11 => 0x7A, Key::F12 => 0x7B,
            Key::Space => 0x20, Key::Return => 0x0D,
            Key::Tab => 0x09, Key::Escape => 0x1B,
            Key::ControlLeft | Key::ControlRight => 0x11,
            Key::Alt => 0x12,
            Key::ShiftLeft | Key::ShiftRight => 0x10,
            Key::CapsLock => 0x14,
            Key::LeftArrow => 0x25, Key::RightArrow => 0x27,
            Key::UpArrow => 0x26, Key::DownArrow => 0x28,
            Key::Backspace => 0x08, Key::Delete => 0x2E,
            _ => {
                let name = format!("{:?}", key);
                if name.len() == 1 {
                    let c = name.chars().next().unwrap();
                    if c.is_ascii_alphabetic() {
                        return c.to_ascii_uppercase() as u32;
                    }
                }
                0
            }
        }
    }

    fn vk_to_key_name(vk: u32) -> String {
        match vk {
            0x70 => "F1".to_string(), 0x71 => "F2".to_string(), 0x72 => "F3".to_string(),
            0x73 => "F4".to_string(), 0x74 => "F5".to_string(), 0x75 => "F6".to_string(),
            0x76 => "F7".to_string(), 0x77 => "F8".to_string(), 0x78 => "F9".to_string(),
            0x79 => "F10".to_string(), 0x7A => "F11".to_string(), 0x7B => "F12".to_string(),
            0x20 => "Space".to_string(), 0x0D => "Enter".to_string(), 0x09 => "Tab".to_string(),
            0x1B => "Esc".to_string(), 0x11 => "Ctrl".to_string(), 0x12 => "Alt".to_string(),
            0x10 => "Shift".to_string(), 0x14 => "CapsLock".to_string(), 0x25 => "Left".to_string(),
            0x27 => "Right".to_string(), 0x26 => "Up".to_string(), 0x28 => "Down".to_string(),
            0x08 => "Backspace".to_string(), 0x2E => "Delete".to_string(),
            0x30..=0x39 => format!("Num{}", vk - 0x30),
            _ => format!("VK={}", vk),
        }
    }

    /// Send a left mouse click via `SendInput`.
    /// Returns true if both events were successfully processed.
    #[must_use]
    fn send_click() -> bool {
        let inputs: [INPUT; 2] = [
            INPUT {
                r#type: INPUT_MOUSE,
                Anonymous: INPUT_0 {
                    mi: MOUSEINPUT {
                        dwFlags: MOUSEEVENTF_LEFTDOWN,
                        ..Default::default()
                    },
                },
            },
            INPUT {
                r#type: INPUT_MOUSE,
                Anonymous: INPUT_0 {
                    mi: MOUSEINPUT {
                        dwFlags: MOUSEEVENTF_LEFTUP,
                        ..Default::default()
                    },
                },
            },
        ];
        let result = unsafe {
            SendInput(&inputs, std::mem::size_of::<INPUT>() as i32)
        };
        result == 2
    }

    /// Send a single key press (down + up) for the given virtual-key code via `SendInput`.
    /// Returns true if both events were successfully processed.
    #[must_use]
    fn send_key_press(vk_code: u32) -> bool {
        let vk = VIRTUAL_KEY(vk_code as u16);
        let inputs: [INPUT; 2] = [
            INPUT {
                r#type: INPUT_KEYBOARD,
                Anonymous: INPUT_0 {
                    ki: KEYBDINPUT {
                        wVk: vk,
                        wScan: 0,
                        dwFlags: Default::default(), // key down
                        time: 0,
                        dwExtraInfo: 0,
                    },
                },
            },
            INPUT {
                r#type: INPUT_KEYBOARD,
                Anonymous: INPUT_0 {
                    ki: KEYBDINPUT {
                        wVk: vk,
                        wScan: 0,
                        dwFlags: KEYEVENTF_KEYUP,
                        time: 0,
                        dwExtraInfo: 0,
                    },
                },
            },
        ];
        let result = unsafe {
            SendInput(&inputs, std::mem::size_of::<INPUT>() as i32)
        };
        result == 2
    }

    #[inline]
    fn get_cps(&self) -> f32 {
        f32::from_bits(self.cps_value.load(Ordering::Relaxed))
    }

    #[inline]
    fn is_slow_mode(&self) -> bool {
        self.mode.load(Ordering::Relaxed) == 1
    }
}

/// Wrapper for click sending with logging of failures.
fn send_mouse_click() {
    if !SharedState::send_click() {
        eprintln!("Warning: SendInput failed to send click events");
    }
}

/// Wrapper for sending a macro's recorded key press, with logging of failures.
fn send_macro_key(vk_code: u32) {
    if !SharedState::send_key_press(vk_code) {
        eprintln!("Warning: SendInput failed to send macro key press");
    }
}

/// Maps an egui key event (only ever delivered while our window has focus)
/// to the same VK-code space used everywhere else in this file.
fn egui_key_to_vk(key: egui::Key) -> u32 {
    use egui::Key as K;
    match key {
        K::Num0 => 0x30, K::Num1 => 0x31, K::Num2 => 0x32,
        K::Num3 => 0x33, K::Num4 => 0x34, K::Num5 => 0x35,
        K::Num6 => 0x36, K::Num7 => 0x37, K::Num8 => 0x38,
        K::Num9 => 0x39,
        K::F1 => 0x70, K::F2 => 0x71, K::F3 => 0x72,
        K::F4 => 0x73, K::F5 => 0x74, K::F6 => 0x75,
        K::F7 => 0x76, K::F8 => 0x77, K::F9 => 0x78,
        K::F10 => 0x79, K::F11 => 0x7A, K::F12 => 0x7B,
        K::Space => 0x20, K::Enter => 0x0D,
        K::Tab => 0x09, K::Escape => 0x1B,
        K::ArrowLeft => 0x25, K::ArrowRight => 0x27,
        K::ArrowUp => 0x26, K::ArrowDown => 0x28,
        K::Backspace => 0x08, K::Delete => 0x2E,
        K::Insert => 0x2D, K::Home => 0x24, K::End => 0x23,
        K::PageUp => 0x21, K::PageDown => 0x22,
        K::A => 0x41, K::B => 0x42, K::C => 0x43, K::D => 0x44,
        K::E => 0x45, K::F => 0x46, K::G => 0x47, K::H => 0x48,
        K::I => 0x49, K::J => 0x4A, K::K => 0x4B, K::L => 0x4C,
        K::M => 0x4D, K::N => 0x4E, K::O => 0x4F, K::P => 0x50,
        K::Q => 0x51, K::R => 0x52, K::S => 0x53, K::T => 0x54,
        K::U => 0x55, K::V => 0x56, K::W => 0x57, K::X => 0x58,
        K::Y => 0x59, K::Z => 0x5A,
        _ => 0,
    }
}

/// Handles the *global* low-level hook path — this only ever fires the
/// autoclicker / macro-master-switch toggle hotkeys, and only while our own
/// window does NOT have OS focus.
///
/// Rebinding a hotkey and recording a macro key are NOT handled here anymore.
/// On Windows, a `WH_KEYBOARD_LL` hook installed from a background thread can
/// be starved while the hooking app's own window has input focus (winit/the
/// OS message pump for the focused window gets first crack at the input), so
/// relying on this hook for "press the key you want to bind" only worked
/// while some other window was focused — exactly the bug reported. Anything
/// that needs to happen while the user is looking at this app (recording,
/// rebinding, and even the toggle hotkeys themselves) is captured directly
/// from egui's own input queue in `update()` instead, which is reliable
/// regardless of any global hook quirks. This function is the fallback for
/// when the window is unfocused (e.g. while a game is in the foreground).
fn global_key_handler(state: &SharedState, key: &Key) {
    // The egui-side capture in `update()` already covers everything while
    // we're focused. Skip here to avoid double-toggling the same key press.
    if state.window_focused.load(Ordering::Relaxed) {
        return;
    }

    let vk = SharedState::key_to_vk_code(key);
    if vk == 0 {
        return;
    }

    if vk == state.autoclicker_key.load(Ordering::Relaxed) {
        state.is_running.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |v| Some(!v)).ok();
        return;
    }

    if vk == state.master_switch_key.load(Ordering::Relaxed) {
        state.macros_enabled.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |v| Some(!v)).ok();
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tab {
    Autoclicker,
    Macros,
    Settings,
}

struct AutoclickerApp {
    state: Arc<SharedState>,
    clicker_thread: Option<thread::JoinHandle<()>>,
    macro_executors: HashMap<u32, thread::JoinHandle<()>>,
    macro_shutdowns: Arc<Mutex<HashMap<u32, Arc<AtomicBool>>>>,
    feedback_message: String,
    feedback_start: Option<Instant>,
    selected_tab: Tab,
    hwnd_initialized: bool,
}

impl AutoclickerApp {
    fn new(_cc: &eframe::CreationContext<'_>) -> Self {
        let state = Arc::new(SharedState::new());
        let macro_shutdowns: Arc<Mutex<HashMap<u32, Arc<AtomicBool>>>> =
            Arc::new(Mutex::new(HashMap::new()));

        let state_clicker = state.clone();
        let clicker_thread = thread::Builder::new()
            .name("clicker".to_string())
            .spawn(move || {
                let mut last_click = Instant::now();
                while !state_clicker.shutdown.load(Ordering::Relaxed) {
                    if state_clicker.is_running.load(Ordering::Relaxed) {
                        let interval = if state_clicker.is_slow_mode() {
                            Duration::from_secs_f32(
                                f32::from_bits(state_clicker.slow_value.load(Ordering::Relaxed)),
                            )
                        } else {
                            let cps = state_clicker.get_cps();
                            // CPS is clamped to 0.1..=1000.0 by the UI, so cps is always > 0.0.
                            Duration::from_secs_f32(1.0 / cps)
                        };

                        let now = Instant::now();
                        if now >= last_click + interval {
                            send_mouse_click();
                            last_click = now;
                        } else {
                            let remaining = interval.saturating_sub(now.duration_since(last_click));
                            thread::park_timeout(remaining.min(Duration::from_millis(10)));
                        }
                    } else {
                        thread::park_timeout(Duration::from_millis(100));
                        last_click = Instant::now();
                    }
                }
            })
            .unwrap();

        // Spawn the global key listener as a detached thread.
        // `rdev::listen` blocks forever on a Windows message loop, so we cannot join it.
        // On process exit the OS will clean up the hook.
        // We store no handle — the Arc references keep SharedState alive.
        let state_listener = state.clone();
        thread::Builder::new()
            .name("listener".to_string())
            .spawn(move || {
                if let Err(e) = listen(move |event| {
                    if state_listener.shutdown.load(Ordering::Relaxed) {
                        return;
                    }
                    if let EventType::KeyPress(key) = event.event_type {
                        global_key_handler(&state_listener, &key);
                    }
                }) {
                    eprintln!("Global key listener error: {:?}", e);
                }
            })
            .unwrap();

        Self {
            state,
            clicker_thread: Some(clicker_thread),
            macro_executors: HashMap::new(),
            macro_shutdowns,
            feedback_message: String::new(),
            feedback_start: None,
            selected_tab: Tab::Autoclicker,
            hwnd_initialized: false,
        }
    }

    fn start_macro_executor(&mut self, macro_id: u32) {
        self.stop_macro_executor(macro_id);

        let state = self.state.clone();
        let shutdown_flag = Arc::new(AtomicBool::new(false));
        {
            let mut shutdowns = self.macro_shutdowns.lock();
            shutdowns.insert(macro_id, shutdown_flag.clone());
        }

        let handle = thread::Builder::new()
            .name(format!("macro-{}", macro_id))
            .spawn(move || {
                // Track macro state locally to avoid reading SharedState every iteration
                let mut last_press = Instant::now();

                while !state.shutdown.load(Ordering::Relaxed)
                    && !shutdown_flag.load(Ordering::Relaxed)
                {
                    let (should_run, interval, recorded_key) = match state.get_macro(macro_id) {
                        Some(m)
                            if m.state == MacroButtonState::Running
                                && state.macros_enabled.load(Ordering::Relaxed) =>
                        {
                            let limited =
                                m.repeat_count > 0 && m.repetition_count >= m.repeat_count;
                            (
                                !limited,
                                Duration::from_secs_f32(m.repeat_interval.max(0.001)),
                                m.recorded_key,
                            )
                        }
                        _ => (false, Duration::from_millis(50), None),
                    };

                    if should_run {
                        let now = Instant::now();
                        if now >= last_press + interval {
                            if let Some(key) = recorded_key {
                                send_macro_key(key.vk_code);
                            }
                            state.modify_macro(macro_id, |m| {
                                m.repetition_count = m.repetition_count.saturating_add(1);
                            });
                            last_press = now;
                        } else {
                            let remaining = interval.saturating_sub(now.duration_since(last_press));
                            thread::park_timeout(remaining.min(Duration::from_millis(10)));
                        }
                    } else {
                        thread::park_timeout(Duration::from_millis(100));
                    }
                }
            })
            .unwrap();
        self.macro_executors.insert(macro_id, handle);
    }

    fn stop_macro_executor(&mut self, macro_id: u32) {
        if let Some(shutdown) = {
            let mut shutdowns = self.macro_shutdowns.lock();
            shutdowns.remove(&macro_id)
        } {
            shutdown.store(true, Ordering::Relaxed);
        }
        if let Some(handle) = self.macro_executors.remove(&macro_id) {
            let _ = handle.join();
        }
    }

    fn stop_all_macros(&mut self) {
        let ids: Vec<u32> = self.macro_executors.keys().copied().collect();
        for id in ids {
            self.stop_macro_executor(id);
        }
    }

    fn set_feedback(&mut self, msg: String) {
        self.feedback_message = msg;
        self.feedback_start = Some(Instant::now());
    }

    fn ui_autoclicker_tab(&mut self, ui: &mut egui::Ui) {
        let is_running = self.state.is_running.load(Ordering::Relaxed);

        ui.label("Autoclicker Controls");
        ui.add_space(5.0);

        ui.label("Mode:");
        let mut selected_mode = self.state.mode.load(Ordering::Relaxed);
        let mut cps: f32 = f32::from_bits(self.state.cps_value.load(Ordering::Relaxed));
        let mut slow: f32 = f32::from_bits(self.state.slow_value.load(Ordering::Relaxed));

        ui.selectable_value(&mut selected_mode, 0, "CPS Mode");
        ui.selectable_value(&mut selected_mode, 1, "Slow Mode");
        self.state.mode.store(selected_mode, Ordering::Relaxed);

        if selected_mode == 1 {
            ui.label("Click Interval (seconds):");
            if ui.add(egui::DragValue::new(&mut slow).speed(0.1).clamp_range(0.1..=3600.0)).changed() {
                self.state.slow_value.store(slow.to_bits(), Ordering::Relaxed);
            }
        } else {
            ui.label("CPS (Clicks per Second):");
            if ui.add(egui::DragValue::new(&mut cps).speed(0.1).clamp_range(0.1..=1000.0)).changed() {
                self.state.cps_value.store(cps.to_bits(), Ordering::Relaxed);
            }
        }

        ui.add_space(10.0);

        let mode_name = if self.state.is_slow_mode() { "SLOW" } else { "CPS" };
        ui.label(format!("Mode: {} ", mode_name));
        ui.label(if is_running { "Status: RUNNING" } else { "Status: STOPPED" });

        ui.add_space(10.0);

        if ui.button(if is_running { "Stop Clicking" } else { "Start Clicking" }).clicked() {
            self.state.is_running.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |v| Some(!v)).ok();
        }
    }

    fn ui_macros_tab(&mut self, ui: &mut egui::Ui) {
        ui.label("Macro Controls");
        ui.add_space(5.0);

        let macro_count = self.state.macro_count();
        ui.label(format!("Active Macros: {}/{}", macro_count, MAX_MACROS));

        let can_add = macro_count < MAX_MACROS;
        let add_label = if !can_add { "Add Macro (+) [disabled]" } else { "Add Macro (+)" };
        if ui.button(add_label).clicked() && can_add {
            let new_id = self.state.add_macro();
            if new_id != 0 {
                self.set_feedback(format!("Added macro #{}", new_id));
            }
        }

        ui.add_space(10.0);

        let master_on = self.state.macros_enabled.load(Ordering::Relaxed);
        let master_key_name = SharedState::vk_to_key_name(self.state.master_switch_key.load(Ordering::Relaxed));
        if master_on {
            ui.colored_label(egui::Color32::GREEN, format!("Master Switch: ON  (press {} to disable)", master_key_name));
        } else {
            ui.colored_label(egui::Color32::YELLOW, format!("Master Switch: OFF — armed macros will NOT fire until you press {}", master_key_name));
        }

        ui.add_space(10.0);

        // Snapshot all macros sorted by ID — avoids N+1 mutex acquisitions per frame.
        let macros_snapshot = self.state.snapshot_sorted();
        if !macros_snapshot.is_empty() {
            for m in &macros_snapshot {
                let macro_id = m.id;
                ui.push_id(macro_id, |ui| {
                    ui.horizontal(|ui| {
                        ui.label(format!("Macro #{}", macro_id));
                        if ui.button("Remove").clicked() {
                            self.stop_macro_executor(macro_id);
                            self.state.remove_macro(macro_id);
                            if self.state.get_current_macro_id() == macro_id {
                                self.state.set_current_macro_id(0);
                            }
                            self.set_feedback(format!("Removed macro #{}", macro_id));
                        }
                    });
                    ui.add_space(5.0);

                    let state_str = match m.state {
                        MacroButtonState::Idle => "Idle".to_string(),
                        MacroButtonState::WaitingKey => "Waiting for key...".to_string(),
                        MacroButtonState::Running => {
                            let total = if m.repeat_count == 0 { "∞".to_string() } else { m.repeat_count.to_string() };
                            format!("Running ({}/{})", m.repetition_count, total)
                        }
                    };
                    ui.label(format!("State: {}", state_str));

                    if let Some(ref key) = m.recorded_key {
                        ui.label(format!("Recorded key: VK={}", key.vk_code));
                    }

                    ui.add_space(5.0);

                    ui.horizontal(|ui| {
                        if ui.button("Set Current").clicked() {
                            self.state.set_current_macro_id(macro_id);
                            self.set_feedback(format!("Macro #{} is now current", macro_id));
                        }
                    });

                    ui.add_space(5.0);

                    let mut macro_cps: f32 = if m.repeat_interval > 0.0 { 1.0 / m.repeat_interval } else { 1.0 };
                    ui.horizontal(|ui| {
                        ui.label("CPS (Clicks per Second):");
                        if ui.add(egui::DragValue::new(&mut macro_cps).speed(0.1).clamp_range(0.1..=1000.0)).changed() {
                            let new_rate = 1.0 / macro_cps.max(0.1);
                            self.state.modify_macro(macro_id, |m| {
                                m.repeat_interval = new_rate;
                            });
                        }
                    });

                    let mut repeat_count = m.repeat_count as f64;
                    ui.horizontal(|ui| {
                        ui.label("Repeat Count (0=infinite):");
                        if ui.add(egui::Slider::new(&mut repeat_count, 0.0..=1000.0).step_by(1.0)).changed() {
                            self.state.modify_macro(macro_id, |m| {
                                m.repeat_count = repeat_count as u32;
                            });
                        }
                    });

                    ui.horizontal(|ui| {
                        ui.label("Press ");
                        let start_stop_resp = ui.add(egui::Button::new("Start/Stop"));
                        if start_stop_resp.clicked() {
                            // Crucial: a focused button is reactivated by egui itself when
                            // Space or Enter is pressed (see egui::Response::clicked() docs).
                            // If we left this button focused, recording Space/Enter as the
                            // macro key would ALSO re-click "Start/Stop" the same frame,
                            // instantly undoing the state change we're about to make below.
                            start_stop_resp.surrender_focus();

                            let mut should_stop = false;
                            let mut should_start = false;
                            self.state.modify_macro(macro_id, |m| {
                                match m.state {
                                    MacroButtonState::Idle => {
                                        m.state = MacroButtonState::WaitingKey;
                                        m.repetition_count = 0;
                                        should_start = true;
                                    }
                                    MacroButtonState::WaitingKey | MacroButtonState::Running => {
                                        m.state = MacroButtonState::Idle;
                                        m.recorded_key = None;
                                        m.repetition_count = 0;
                                        should_stop = true;
                                    }
                                }
                            });
                            if should_stop {
                                self.stop_macro_executor(macro_id);
                                self.set_feedback(format!("Macro #{} stopped", macro_id));
                            }
                            if should_start {
                                self.set_feedback(format!("Macro #{}: press a key to record", macro_id));
                            }
                        }
                    });

                    ui.add_space(10.0);
                    ui.separator();
                    ui.add_space(10.0);
                });
            }
        } else {
            ui.label("No macros defined. Click '+' to add one.");
        }

        ui.add_space(20.0);
        ui.label("Usage:");
        ui.label("1. Click '+' to add a macro button");
        ui.label("2. Click 'Set Current' to select the macro to control");
        ui.label("3. Click 'Start/Stop' to start recording a key to repeat");
        ui.label("4. Press the desired key (e.g. 'C') while the macro is current");
        ui.label("5. Configure repeat rate and count");
        ui.label("6. Press the Master Switch key (default F7) to enable playback");
        ui.label("   — recorded macros stay armed but silent until you do this");
    }

    fn ui_settings_tab(&mut self, ui: &mut egui::Ui) {
        ui.label("Settings");
        ui.add_space(5.0);

        ui.label("Key Bindings");
        ui.add_space(5.0);

        ui.horizontal(|ui| {
            let current_key = SharedState::vk_to_key_name(self.state.autoclicker_key.load(Ordering::Relaxed));
            ui.label(format!("Autoclicker Toggle: {}", current_key));
            let change_resp = ui.button("Change");
            if change_resp.clicked() {
                change_resp.surrender_focus();
                self.state.rebinding_target.store(1, Ordering::Relaxed);
                self.set_feedback("Press new key for Autoclicker...".to_string());
            }
        });

        ui.horizontal(|ui| {
            let current_key = SharedState::vk_to_key_name(self.state.master_switch_key.load(Ordering::Relaxed));
            ui.label(format!("Macro Master Switch: {}", current_key));
            let change_resp = ui.button("Change");
            if change_resp.clicked() {
                change_resp.surrender_focus();
                self.state.rebinding_target.store(2, Ordering::Relaxed);
                self.set_feedback("Press new key for Macro Switch...".to_string());
            }
            let master_on = self.state.macros_enabled.load(Ordering::Relaxed);
            ui.colored_label(
                if master_on { egui::Color32::GREEN } else { egui::Color32::GRAY },
                if master_on { "(ON)" } else { "(OFF)" },
            );
        });

        if self.state.rebinding_target.load(Ordering::Relaxed) != 0 {
            ui.add_space(5.0);
            ui.colored_label(egui::Color32::YELLOW, "WAITING FOR KEY PRESS...");
        }

        ui.add_space(15.0);
        ui.separator();
        ui.add_space(5.0);

        // --- Failsafe Section ---
        ui.label("Failsafe");
        ui.add_space(5.0);

        let mut failsafe_on = self.state.failsafe_enabled.load(Ordering::Relaxed);
        if ui.checkbox(&mut failsafe_on, "Auto-stop on window unfocus (alt+tab, win+d, ctrl+alt+del, etc.)").clicked() {
            self.state.failsafe_enabled.store(failsafe_on, Ordering::Relaxed);
        }

        let status_text = if failsafe_on {
            "✅ Failsafe is ON — Autoclicker and macros will auto-stop when window loses focus."
        } else {
            "❌ Failsafe is OFF — Autoclicker and macros will continue even when window is unfocused."
        };
        if failsafe_on {
            ui.colored_label(egui::Color32::GREEN, status_text);
        } else {
            ui.colored_label(egui::Color32::GRAY, status_text);
        }

        ui.add_space(10.0);
        ui.label("Note: Press the key to toggle the respective feature.");
    }
}

// --- Drop ---
impl Drop for AutoclickerApp {
    fn drop(&mut self) {
        self.state.is_running.store(false, Ordering::Relaxed);
        self.state.shutdown.store(true, Ordering::Relaxed);
        self.stop_all_macros();
        if let Some(h) = self.clicker_thread.take() {
            // Unpark the clicker thread so it notices the shutdown flag
            h.thread().unpark();
            let _ = h.join();
        }
        // Listener thread is detached — it will be cleaned up when the process exits.
        // The Arc<SharedState> keeps it alive until then.
    }
}

// --- Entry point ---
fn load_icon() -> egui::IconData {
    let icon_bytes = include_bytes!("icon.png");
    let img = image::load_from_memory(icon_bytes)
        .expect("Failed to load icon.png — ensure it is a valid PNG file");
    let rgba = img.into_rgba8();
    let width = rgba.width();
    let height = rgba.height();
    egui::IconData {
        rgba: rgba.into_raw(),
        width,
        height,
    }
}

fn main() -> Result<(), eframe::Error> {
    let icon = std::sync::Arc::new(load_icon());
    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_inner_size([420.0, 420.0])
            .with_icon(icon),
        ..Default::default()
    };
    eframe::run_native(
        "Rust Autoclicker with Macros",
        options,
        Box::new(|cc| {
            // Load and set Roboto font (embedded at compile time — no runtime file dependency)
            let roboto_bytes = include_bytes!("Roboto-Regular.ttf");
            let mut fonts = egui::FontDefinitions::default();
            fonts.font_data.insert(
                "Roboto".into(),
                egui::FontData::from_owned(roboto_bytes.to_vec()),
            );
            fonts
                .families
                .insert(egui::FontFamily::Proportional, vec!["Roboto".into()]);
            fonts
                .families
                .insert(egui::FontFamily::Monospace, vec!["Roboto".into()]);
            cc.egui_ctx.set_fonts(fonts);

            // Set professional dark background
            let mut visuals = egui::Visuals::dark();
            visuals.panel_fill = egui::Color32::from_rgb(18, 18, 18);
            visuals.window_fill = egui::Color32::from_rgb(22, 22, 22);
            cc.egui_ctx.set_visuals(visuals);

            Box::new(AutoclickerApp::new(cc))
        }),
    )
}

// --- GUI ---
impl App for AutoclickerApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut Frame) {
        // Initialize the HWND once we have a window (needed for failsafe focus detection)
        if !self.hwnd_initialized {
            unsafe {
                let hwnd_isize = GetActiveWindow().0 as isize;
                if hwnd_isize != 0 {
                    self.state.target_hwnd.store(hwnd_isize, Ordering::Relaxed);
                    self.hwnd_initialized = true;
                }
            }
        }

        // GUI thread owns failsafe writes — updates the cached focus flag
        // and stops everything on focus loss. Workers only read the flag.
        if self.hwnd_initialized {
            self.state.update_failsafe_from_gui();
        }

        // --- In-window key capture ---
        // Reads key presses straight from egui's own input queue instead of
        // the global rdev hook. On Windows the global low-level hook can be
        // starved while THIS window has input focus, which is exactly why
        // macro recording/rebinding used to silently fail unless you
        // alt-tabbed away. egui always sees its own window's key events
        // reliably, so everything that needs to happen while the user is
        // looking at the app — rebinding a hotkey, recording a macro key,
        // and the toggle hotkeys themselves — is handled here. The global
        // hook (`global_key_handler`) only takes over once this window
        // loses focus (e.g. a game is in the foreground), and explicitly
        // skips while focused so the two paths never double-fire.
        if self.state.window_focused.load(Ordering::Relaxed) {
            let key_presses: Vec<egui::Key> = ctx.input(|i| {
                i.events.iter().filter_map(|e| match e {
                    egui::Event::Key { key, pressed: true, repeat: false, .. } => Some(*key),
                    _ => None,
                }).collect()
            });
            // A text/number field currently being typed into "claims" plain
            // letter/number keys, so we don't let those accidentally trigger
            // a toggle hotkey. Rebinding and macro-key recording always take
            // priority since they're an explicit, deliberate action.
            let editing_widget = ctx.memory(|m| m.focused().is_some());

            for key in key_presses {
                let vk = egui_key_to_vk(key);
                if vk == 0 {
                    continue;
                }

                let rebind_target = self.state.rebinding_target.load(Ordering::Relaxed);
                if rebind_target != 0 {
                    if rebind_target == 1 {
                        self.state.autoclicker_key.store(vk, Ordering::Relaxed);
                        self.set_feedback(format!("Autoclicker key set to {}", SharedState::vk_to_key_name(vk)));
                    } else if rebind_target == 2 {
                        self.state.master_switch_key.store(vk, Ordering::Relaxed);
                        self.set_feedback(format!("Macro master switch key set to {}", SharedState::vk_to_key_name(vk)));
                    }
                    self.state.rebinding_target.store(0, Ordering::Relaxed);
                    continue;
                }

                let current_macro_id = self.state.get_current_macro_id();
                let mut recorded = false;
                if current_macro_id != 0 {
                    self.state.modify_macro(current_macro_id, |m| {
                        if m.state == MacroButtonState::WaitingKey {
                            m.recorded_key = Some(MacroKeyPress { vk_code: vk });
                            m.state = MacroButtonState::Running;
                            recorded = true;
                        }
                    });
                }
                if recorded {
                    self.start_macro_executor(current_macro_id);
                    self.set_feedback(format!(
                        "Key {} recorded for macro #{}",
                        SharedState::vk_to_key_name(vk),
                        current_macro_id
                    ));
                    continue;
                }

                if editing_widget {
                    continue;
                }
                if vk == self.state.autoclicker_key.load(Ordering::Relaxed) {
                    self.state.is_running.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |v| Some(!v)).ok();
                } else if vk == self.state.master_switch_key.load(Ordering::Relaxed) {
                    self.state.macros_enabled.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |v| Some(!v)).ok();
                }
            }
        }

        egui::CentralPanel::default().show(ctx, |ui| {
            egui::ScrollArea::vertical().show(ui, |ui| {
                // Feedback message with Instant-based expiry (visible for 2 seconds)
                if let Some(start) = self.feedback_start {
                    if start.elapsed() < FEEDBACK_DURATION {
                        ui.colored_label(egui::Color32::GREEN, &self.feedback_message);
                        ui.add_space(5.0);
                    } else {
                        self.feedback_start = None;
                    }
                }

                ui.horizontal(|ui| {
                    ui.selectable_value(&mut self.selected_tab, Tab::Autoclicker, "Autoclicker");
                    ui.selectable_value(&mut self.selected_tab, Tab::Macros, "Macros");
                    ui.selectable_value(&mut self.selected_tab, Tab::Settings, "Settings");
                });

                ui.add_space(10.0);
                ui.separator();
                ui.add_space(10.0);

                match self.selected_tab {
                    Tab::Autoclicker => self.ui_autoclicker_tab(ui),
                    Tab::Macros => self.ui_macros_tab(ui),
                    Tab::Settings => self.ui_settings_tab(ui),
                }
            });
        });

        // Repaint fast only when something is actively changing;
        // otherwise sleep longer to save CPU.
        let needs_fast_repaint = self.state.is_running.load(Ordering::Relaxed)
            || self.state.macros_enabled.load(Ordering::Relaxed)
            || self.feedback_start.is_some()
            || self.state.rebinding_target.load(Ordering::Relaxed) != 0;

        let repaint_delay = if needs_fast_repaint {
            Duration::from_millis(16) // ~60 FPS
        } else {
            Duration::from_millis(200) // 5 FPS when idle
        };
        ctx.request_repaint_after(repaint_delay);
    }
}