#[cfg(kani)]
pub fn options_new() -> std::fs::OpenOptions {
    std::fs::OpenOptions::new()
}
#[cfg(kani)]
pub fn options_write(options: &mut std::fs::OpenOptions, write: bool) -> &mut std::fs::OpenOptions {
    options.write(write)
}
#[cfg(kani)]
pub fn options_create_new(options: &mut std::fs::OpenOptions, create: bool) -> &mut std::fs::OpenOptions {
    options.create_new(create)
}
#[cfg(kani)]
pub fn options_mode(options: &mut std::fs::OpenOptions, mode: u32) -> &mut std::fs::OpenOptions {
    use std::os::unix::fs::OpenOptionsExt;
    options.mode(mode)
}
