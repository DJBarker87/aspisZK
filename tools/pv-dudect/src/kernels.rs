use source_link::source_module;
source_module!(state_only_hiding, "crates/aspis-prover/src/state_only_hiding.rs", {
    pub struct Input(SeedExpander);
    pub fn prepare(seed: [u8;32], blockmode: u8) -> Input {
        let mut s = SeedExpander::new(aspis_prover::HOST_HASH, seed);
        if blockmode != 0 {
            // Synthetic internal state: fixed canonical block vs one-rejection random block.
            s.block = seed;
            for b in s.block.chunks_exact_mut(4) { b[3] &= 0x3f; }
            if blockmode == 2 { s.block[..4].copy_from_slice(&P.to_le_bytes()); }
            s.word = 0;
        }
        Input(s)
    }
    #[inline(never)] pub fn measure_m31(s: &mut Input) -> Result<M31, StateOnlyMaskBuildError> { s.0.m31() }
    #[inline(never)] pub fn measure_qm31(s: &mut Input) -> Result<QM31, StateOnlyMaskBuildError> { s.0.qm31() }
});
source_module!(entropy, "crates/aspis-prover/src/state_only_entropy.rs", {
    // Isolate each actual private-seed predicate used by generate_for_mask_nonce.
    // The OS fill and retry/short-circuit composition are NOT measured here.
    #[inline(never)] pub fn seed_check(seed: &[u8;32]) -> bool { entropy_nonzero32(seed) }
});
#[path = "../../../crates/aspis-r1-cost-probe/src/ct_pole.rs"]
pub mod ct_pole;
#[path = "../../../crates/aspis-r1-cost-probe/src/prover_shared.rs"]
pub mod prover_shared;
pub use state_only_hiding::{prepare, measure_m31, measure_qm31};
pub use entropy::seed_check;
