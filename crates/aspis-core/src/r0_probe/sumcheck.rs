//! Unproved COST PROBE; unchanged S4 round checks and evaluation.
use super::mark;
use super::prefix::{decode_values, Error, Prefix, SemanticTranscript};
use crate::field::{WideExact, QM31};
pub type Polynomial = [WideExact; 28];
pub fn boundary(poly: &Polynomial) -> WideExact {
    poly.iter().copied().fold(poly[0], WideExact::add)
}
pub fn evaluate(poly: &Polynomial, alpha: QM31) -> WideExact {
    let x = WideExact::from_qm31(alpha);
    poly.iter()
        .rev()
        .fold(WideExact::ZERO, |acc, c| acc.mul(x).add(*c))
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Verification {
    pub alpha: [QM31; 10],
    pub terminal_claim: WideExact,
}
pub fn verify(
    prefix: &Prefix<'_>,
    transcript: &mut SemanticTranscript,
) -> Result<Verification, Error> {
    mark("r0:b:+sem.sumcheck_decode_initial");
    let mut running = decode_values::<1>(14, prefix.payload(14)?)?[0];
    mark("r0:b:-sem.sumcheck_decode_initial");
    let mut alpha = [QM31::ZERO; 10];
    for (round, challenge) in alpha.iter_mut().enumerate() {
        let row = 15 + round as u8;
        mark("r0:b:+sem.sumcheck_decode");
        let poly = decode_values::<28>(row, prefix.payload(row)?)?;
        mark("r0:b:-sem.sumcheck_decode");
        mark("r0:b:+sem.boundary_checks");
        if boundary(&poly) != running {
            return Err(Error::Boundary { round });
        }
        mark("r0:b:-sem.boundary_checks");
        *challenge = transcript.semantic(row, prefix.record(row)?)?;
        mark("r0:b:+sem.alpha_evaluation");
        running = evaluate(&poly, *challenge);
        mark("r0:b:-sem.alpha_evaluation");
    }
    Ok(Verification {
        alpha,
        terminal_claim: running,
    })
}
