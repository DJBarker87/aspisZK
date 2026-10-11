//! UNPROVED COST PROBE. P2 semantic layer in K plus the specified D14 tail.
use alloc::boxed::Box;
use aspis_core::{circle::SecureCirclePoint, field::QM31, HashFn};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
use crate::r1_wire::{self as wire, Challenges, Error, Prefix, SemanticTranscript};

pub struct Verified {
    pub roots: [[u8; 32]; 2],
    pub challenges: Challenges,
    pub alpha: [QM31; 10],
    pub claims: Box<[[QM31; 29]; 3]>,
    pub extra: [QM31; 29],
    pub before_z1: [QM31; 29],
    pub state_before_z0: [u8; 32],
    pub z: [SecureCirclePoint; 2],
    pub transcript: SemanticTranscript,
    #[cfg(feature="prover")]
    pub round_checks: [[QM31; 3]; 10],
    #[cfg(feature="prover")]
    pub terminal: QM31,
    #[cfg(feature="prover")]
    pub masked_terminal: QM31,
}

pub fn decode<const N: usize>(row: u8, bytes: &[u8]) -> Result<[QM31; N], Error> {
    if bytes.len() != N * 32 { return Err(Error::Length { row }); }
    let mut out = [QM31::ZERO; N];
    for (value, part) in bytes.chunks_exact(32).enumerate() {
        // Parse has already asserted c1 == 0. Retain the assertion in this
        // public helper as well, so callers cannot accidentally truncate E.
        if part[16..].iter().any(|&b| b != 0) { return Err(Error::NonCanonical { row, value }); }
        out[value] = QM31::from_le_bytes(&part[..16]).ok_or(Error::NonCanonical { row, value })?;
    }
    Ok(out)
}

#[inline(never)]
fn claims(prefix: &Prefix<'_>) -> Result<Box<[[QM31; 29]; 3]>, Error> {
    let bytes = prefix.payload(25)?;
    let mut out = aspis_core::r0::heap::uninit::<[[QM31; 29]; 3]>().map_err(|_| Error::Allocation)?;
    unsafe {
        for p in 0..3 {
            out.as_mut_ptr().cast::<[QM31; 29]>().add(p)
                .write(decode::<29>(25, &bytes[p*29*32..(p+1)*29*32])?);
        }
        Ok(out.assume_init())
    }
}

#[inline(never)]
pub fn verify(public: Public<'_>, bytes: &[u8], hash: HashFn) -> Result<Verified, Error> {
    let prefix = Prefix::parse(bytes)?;
    let mut transcript = SemanticTranscript::new(hash, &public.public_bytes().map_err(|_| Error::Public)?, prefix.c1_root)?;
    let challenges = wire::begin(&prefix, &mut transcript)?;
    let mut running = decode::<1>(14, prefix.payload(14)?)?[0];
    let mut alpha = [QM31::ZERO; 10];
    #[cfg(feature="prover")]
    let mut round_checks = [[QM31::ZERO; 3]; 10];
    for round in 0..10 {
        let row = 15 + round as u8;
        let polynomial = decode::<28>(row, prefix.payload(row)?)?;
        let boundary = polynomial.iter().copied().fold(polynomial[0], QM31::add);
        if boundary != running { return Err(Error::Boundary { round }); }
        alpha[round] = transcript.semantic(row, prefix.record(row)?)?;
        let value = polynomial.iter().rev().fold(QM31::ZERO, |a, &c| a.mul(alpha[round]).add(c));
        #[cfg(feature="prover")]
        { round_checks[round] = [running, boundary, value]; }
        running = value;
    }
    let claims = claims(&prefix)?;
    let original_challenges = aspis_core::state_only_prefix::r0::Challenges {
        lambda: challenges.lambda, chi: challenges.chi, theta: challenges.theta,
        zc: challenges.zc, mu: challenges.mu, eta: challenges.eta,
    };
    let terminal = public.terminal_qm31(&claims, &alpha, &original_challenges).map_err(|_| Error::Public)?;
    let mask = aspis_core::state_only_hiding::state_only_selected_mask_value(
        &core::array::from_fn(|i| claims[0][i]),
        &core::array::from_fn(|i| claims[0][16+i]), claims[0][27], &alpha,
    );
    let extra = decode::<29>(25, &prefix.payload(25)?[87*32..])?;
    let masked_terminal = mask.add(challenges.eta.mul(terminal)).add(extra[28]);
    if running != masked_terminal { return Err(Error::Terminal); }
    let state_before_z0 = transcript.state();
    let z0 = transcript.challenge_reference_circle_point(25, prefix.record(25)?)?;
    let before_z1 = decode::<29>(26, prefix.payload(26)?)?;
    let z1 = transcript.challenge_reference_circle_point(26, prefix.record(26)?)?;
    #[cfg(feature="prover")]
    {
    for (i,x) in [z0.x,z0.y,z1.x,z1.y].into_iter().enumerate() { crate::trace::value(3,i,aspis_core::field::WideExact::from_qm31(x)); }
    for (i,x) in challenges.with_alphas(&alpha).into_iter().enumerate() { crate::trace::value(0,i,x); }
    for (i, row) in round_checks.iter().enumerate() { for (j,x) in row.iter().enumerate() { crate::trace::value(1,3*i+j,aspis_core::field::WideExact::from_qm31(*x)); } }
    crate::trace::value(2,0,aspis_core::field::WideExact::from_qm31(terminal));
    crate::trace::value(2,1,aspis_core::field::WideExact::from_qm31(masked_terminal));
    }
    if z0 == z1 { return Err(Error::EqualCirclePoints); }
    Ok(Verified { roots: [*prefix.c1_root, prefix.payload(2)?.try_into().unwrap()],
        challenges, alpha, claims, extra, before_z1, state_before_z0, z: [z0,z1], transcript,
        #[cfg(feature="prover")] round_checks,
        #[cfg(feature="prover")] terminal,
        #[cfg(feature="prover")] masked_terminal })
}
