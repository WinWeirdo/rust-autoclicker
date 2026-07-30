use winres::WindowsResource;

fn main() {
    // icon.ico must be a real, valid ICO file (containing an ICONDIR header).
    // Renaming a .png to .ico does NOT produce a valid ICO container, and a
    // broken icon resource embeds silently — the exe just falls back to the
    // default icon. Generate icon.ico from src/icon.png with a real tool
    // (e.g. `cargo install ico-builder`, ImageMagick `convert`, or any
    // online PNG->ICO converter) before building.
    // Skip icon embedding if icon.ico is missing — the app still works with
    // the OS default icon. Generate icon.ico from src/icon.png (e.g. via
    // ImageMagick `convert`, or an online PNG→ICO converter) to get a custom
    // .exe icon in Windows Explorer.
    if std::fs::metadata("icon.ico").is_err() {
        println!("cargo:warning=icon.ico not found — .exe will use the default Windows icon. Generate one from src/icon.png to customize.");
        return;
    }

    if let Err(e) = WindowsResource::new().set_icon("icon.ico").compile() {
        println!("cargo:warning=Failed to compile icon resource: {:?}. The build will continue without a custom .exe icon.", e);
    }
}