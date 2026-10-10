//! Unproved COST PROBE. S4 arithmetic copied without optimization for B.
pub use crate::r0::*;
pub mod onchain;
pub mod prefix;
pub mod prover;
pub mod sumcheck;
/// Passive B markers. Native runs have no observer or arithmetic changes.
#[inline(never)]
pub fn mark(label: &str) {
    #[cfg(target_os = "solana")]
    unsafe {
        extern "C" {
            fn sol_log_(message: *const u8, len: u64);
            fn sol_log_compute_units_();
        }
        sol_log_(label.as_ptr(), label.len() as u64);
        sol_log_compute_units_();
    }
    #[cfg(not(target_os = "solana"))]
    let _ = label;
}
