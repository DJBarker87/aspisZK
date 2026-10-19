//! Extraction-only forwarding wrapper; it does not reimplement terminal logic.
use aspis_core::{
    field::QM31,
    state_only_prefix::r0::{Challenges, Error},
};
use crate::pool_v1::pair_forest_semantic_terminal::r0::Public;

/// Forwards the exact production public method so Charon starts at a free function.
pub fn terminal_qm31_probe(
    public: Public<'_>,
    claims: &[[QM31; 29]; 3],
    alpha: &[QM31; 10],
    challenges: &Challenges,
) -> Result<QM31, Error> {
    public.terminal_qm31(claims, alpha, challenges)
}
