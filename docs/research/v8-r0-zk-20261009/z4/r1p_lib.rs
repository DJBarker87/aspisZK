//! Library face of the z4 probe (LOG D38.3): the prover-side P_R1 check of
//! z9e for the R1 cost-probe prover and simulator.  The binary target
//! (`probe.rs`) is unchanged in behaviour.
#[path = "probe.rs"]
mod probe;
pub use probe::r1p::{p_r1_check, p_r1_columns_audit, R1CheckTimes, R1PublicChallenges};
