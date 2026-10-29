//! Local diagnostics have no operand, source error or backtrace storage.
use std::{backtrace::{Backtrace, BacktraceStatus}, fmt, io::Write};

#[derive(Debug, Clone, Copy)]
pub struct Error(&'static str);
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { f.write_str(self.0) }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;
pub fn err<T>(_: T) -> Error { Error("client operation failed") }
macro_rules! anyhow { ($message:literal) => { $crate::diagnostics::Error::literal($message) }; }
macro_rules! ensure { ($condition:expr, $message:literal) => { if !$condition { return Err(anyhow!($message)); } }; }
pub(super) use {anyhow, ensure};
impl Error { pub fn literal(message: &'static str) -> Self { Self(message) } }

pub fn initialize() {
    std::panic::set_hook(Box::new(|_| {
        let _ = std::io::stderr().write_all(b"client panic\n");
    }));
    // First operation before input, errors, workers or witness processing.
    // Rust 1.94.1 caches this disabled state process-wide. Later environment
    // changes cannot enable Backtrace::capture (also used by anyhow).
    std::env::set_var("RUST_BACKTRACE", "0");
    std::env::set_var("RUST_LIB_BACKTRACE", "0");
    if Backtrace::capture().status() != BacktraceStatus::Disabled {
        // Fail closed if an earlier constructor ever primes the std cache.
        std::process::abort();
    }
}
pub fn report(_: Error) {
    let _ = std::io::stderr().write_all(b"client error\n");
}
