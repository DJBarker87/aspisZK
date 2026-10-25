use alloc::boxed::Box;
use aspis_core::{Digest32,circle::SecureCirclePoint,field::QM31};
use crate::r1_wire::{Challenges,SemanticTranscript};
pub struct Verified<H: Digest32> {
    pub roots: [[u8; 32]; 2],
    pub challenges: Challenges,
    pub alpha: [QM31; 10],
    pub claims: Box<[[QM31; 29]; 3]>,
    pub extra: [QM31; 29],
    pub before_z1: [QM31; 29],
    pub state_before_z0: [u8; 32],
    pub z: [SecureCirclePoint; 2],
    pub transcript: SemanticTranscript<H>,
    #[cfg(feature = "prover")]
    pub round_checks: [[QM31; 3]; 10],
    #[cfg(feature = "prover")]
    pub terminal: QM31,
    #[cfg(feature = "prover")]
    pub masked_terminal: QM31,
}
