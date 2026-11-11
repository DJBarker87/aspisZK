//! Library face of the z4 probe (LOG D38.3): the prover-side P_R1 check of
//! z9e for the R1 cost-probe prover and simulator.  The binary target
//! (`probe.rs`) is unchanged in behaviour.
#[path = "probe.rs"]
mod probe;
pub use probe::r1p::{p_r1_check, p_r1_columns_audit, p_r1_core, R1CheckTimes, R1PublicChallenges};

/// pv-rw-d tests: the pure core's verdict with a panic read as a rejection
/// (Lean: `fail`), the core called directly (no shell, no quiet hook).
#[cfg(test)]
fn p_r1_core_verdict(ch: &R1PublicChallenges) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| p_r1_core(ch))).unwrap_or(false)
}

/// pv-rw-d: the pinned source tree, for the differential tests only.
#[cfg(test)]
#[path = "orig/probe.rs"]
#[allow(dead_code, unused)]
mod probe_orig;
#[cfg(test)]
#[path = "r1p_tests.rs"]
mod tests;
