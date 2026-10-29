use std::backtrace::{Backtrace, BacktraceStatus};
use std::sync::{LazyLock, atomic::{AtomicUsize, Ordering}};
static DROPS: AtomicUsize = AtomicUsize::new(0);
struct Payload;
impl Drop for Payload { fn drop(&mut self) { DROPS.fetch_add(1, Ordering::SeqCst); } }
#[derive(Debug)] struct Custom;
impl std::fmt::Display for Custom { fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { f.write_str("custom") } }
impl std::error::Error for Custom {}
impl Drop for Custom { fn drop(&mut self) { DROPS.fetch_add(1, Ordering::SeqCst); } }
unsafe extern "C" { fn __errno_location() -> *mut i32; }
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    assert_eq!(Backtrace::disabled().status(), BacktraceStatus::Disabled);
    let captured = Backtrace::force_capture();
    assert_eq!(captured.status(), BacktraceStatus::Captured);
    // status borrows, and can be repeated without forcing symbol resolution.
    assert_eq!(captured.status(), captured.status());
    for code in [0, 4, -1, i32::MIN, i32::MAX] {
        let before = DROPS.load(Ordering::SeqCst);
        let error = std::io::Error::from_raw_os_error(code);
        assert_eq!(error.raw_os_error(), Some(code));
        assert_eq!(error.kind() == std::io::ErrorKind::Interrupted, code == 4);
        drop(error);
        assert_eq!(DROPS.load(Ordering::SeqCst), before);
    }
    unsafe {
        let errno = __errno_location();
        let saved = *errno;
        for code in [4, 9, -1] {
            *errno = code;
            assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(code));
        }
        *errno = saved;
    }
    for kind in [std::io::ErrorKind::Interrupted, std::io::ErrorKind::WriteZero, std::io::ErrorKind::Other] {
        let before = DROPS.load(Ordering::SeqCst);
        let simple = std::io::Error::from(kind);
        assert_eq!(simple.kind(), kind);
        drop(simple);
        assert_eq!(DROPS.load(Ordering::SeqCst), before);
    }
    let before = DROPS.load(Ordering::SeqCst);
    drop(std::io::Error::new(std::io::ErrorKind::Other, Custom));
    assert_eq!(DROPS.load(Ordering::SeqCst), before + 1);
    let p = Payload;
    let incomplete = LazyLock::new(move || { let _ = &p; 1usize });
    let before = DROPS.load(Ordering::SeqCst);
    drop(incomplete);
    assert_eq!(DROPS.load(Ordering::SeqCst), before + 1);
    let complete = LazyLock::new(|| Payload);
    LazyLock::force(&complete);
    let before = DROPS.load(Ordering::SeqCst);
    drop(complete);
    assert_eq!(DROPS.load(Ordering::SeqCst), before + 1);
    let p = Payload;
    let poisoned = LazyLock::new(move || -> usize { let _ = &p; panic!("init") });
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| LazyLock::force(&poisoned))).is_err());
    let before = DROPS.load(Ordering::SeqCst);
    drop(poisoned);
    assert_eq!(DROPS.load(Ordering::SeqCst), before);
    println!("native-controls: status, OS/custom error drop, incomplete/complete/poisoned lazy drop passed");
}
