//! UNPROVED COST PROBE. P2 semantic layer in K plus the specified D14 tail.
use crate::r1_wire::{self as wire, Challenges, Error, Prefix, SemanticTranscript};
use alloc::boxed::Box;
use aspis_core::{Digest32, circle::SecureCirclePoint, field::QM31};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;

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

pub fn decode<const N: usize>(row: u8, bytes: &[u8]) -> Result<[QM31; N], Error> {
    if bytes.len() != N * 32 {
        return Err(Error::Length { row });
    }
    let mut out = [QM31::ZERO; N];
    for (value, part) in bytes.chunks_exact(32).enumerate() {
        // Parse has already asserted c1 == 0. Retain the assertion in this
        // public helper as well, so callers cannot accidentally truncate E.
        if part[16..].iter().any(|&b| b != 0) {
            return Err(Error::NonCanonical { row, value });
        }
        out[value] = QM31::from_le_bytes(&part[..16]).ok_or(Error::NonCanonical { row, value })?;
    }
    Ok(out)
}

#[inline(never)]
fn claims(prefix: &Prefix<'_>) -> Result<Box<[[QM31; 29]; 3]>, Error> {
    let record = prefix.validated_record(25)?;
    let rows = aspis_core::r0::heap::filled(3, [QM31::ZERO; 29])
        .map_err(|_| Error::Allocation)?;
    let mut out: Box<[[QM31; 29]; 3]> = rows
        .into_boxed_slice()
        .try_into()
        .map_err(|_| Error::Allocation)?;
    for p in 0..3 {
        out[p] = record.decode_k::<29>(p * 29)?;
    }
    Ok(out)
}

#[inline(never)]
pub fn verify<H: Digest32>(public: Public<'_>, bytes: &[u8], hash: H) -> Result<Verified<H>, Error> {
    verify_observed(public, bytes, hash, None)
}

#[inline(always)]
pub fn public_transcript<H: Digest32>(
    public: Public<'_>,
    hash: H,
    c1_root: &[u8; 32],
) -> Result<SemanticTranscript<H>, Error> {
    SemanticTranscript::new(
        hash,
        &public.public_bytes().map_err(|_| Error::Public)?,
        c1_root,
    )
}

fn mark(obs: crate::verifier::Observer, i: u8) {
    #[cfg(feature="detail-phases")]
    if let Some(f)=obs {f(crate::verifier::Phase::SemanticPart(i));}
    #[cfg(not(feature="detail-phases"))]
    let _=(obs,i);
}

fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {
        let boundary = polynomial.iter().copied().fold(polynomial[0], QM31::add);
    boundary
}

fn semantic_value(polynomial: &[QM31; 28], alpha: &[QM31; 10], round: usize) -> QM31 {
        let value = polynomial
            .iter()
            .rev()
            .fold(QM31::ZERO, |a, &c| a.mul(alpha[round]).add(c));
    value
}

#[cfg(not(feature = "prover"))]
fn semantic_round<H: Digest32>(prefix: &Prefix<'_>, mut transcript: SemanticTranscript<H>, mut alpha: [QM31; 10], mut running: QM31, round: usize) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>), Error> {
        let row = 15 + round as u8;
        let polynomial = prefix.validated_record(row)?.decode_k::<28>(0)?;
        let boundary = semantic_boundary(&polynomial);
        if boundary != running {
            return Err(Error::Boundary { round });
        }
        alpha[round] = transcript.semantic_validated(prefix.validated_record(row)?)?;
        let value = semantic_value(&polynomial, &alpha, round);
        #[cfg(feature = "prover")]
        {
            round_checks[round] = [running, boundary, value];
        }
        running = value;
    Ok((running, alpha, transcript))
}

#[cfg(feature = "prover")]
fn semantic_round<H: Digest32>(prefix: &Prefix<'_>, mut transcript: SemanticTranscript<H>, mut alpha: [QM31; 10], mut running: QM31, round: usize, mut round_checks: [[QM31; 3]; 10]) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>, [[QM31; 3]; 10]), Error> {
        let row = 15 + round as u8;
        let polynomial = prefix.validated_record(row)?.decode_k::<28>(0)?;
        let boundary = semantic_boundary(&polynomial);
        if boundary != running {
            return Err(Error::Boundary { round });
        }
        alpha[round] = transcript.semantic_validated(prefix.validated_record(row)?)?;
        let value = semantic_value(&polynomial, &alpha, round);
        #[cfg(feature = "prover")]
        {
            round_checks[round] = [running, boundary, value];
        }
        running = value;
    Ok((running, alpha, transcript, round_checks))
}

#[cfg(not(feature = "prover"))]
#[inline(never)]
fn semantic_rounds<H: Digest32>(prefix: &Prefix<'_>, mut transcript: SemanticTranscript<H>) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>), Error> {
    let mut running = prefix.validated_record(14)?.decode_k::<1>(0)?[0];
    let mut alpha = [QM31::ZERO; 10];
    #[cfg(feature = "prover")]
    let mut round_checks = [[QM31::ZERO; 3]; 10];
    {
        let round = 0usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 1usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 2usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 3usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 4usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 5usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 6usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 7usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 8usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    {
        let round = 9usize;
        (running, alpha, transcript) = semantic_round(prefix, transcript, alpha, running, round)?;
    }
    Ok((running, alpha, transcript))
}

#[cfg(feature = "prover")]
#[inline(never)]
fn semantic_rounds<H: Digest32>(prefix: &Prefix<'_>, mut transcript: SemanticTranscript<H>) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>, [[QM31; 3]; 10]), Error> {
    let mut running = prefix.validated_record(14)?.decode_k::<1>(0)?[0];
    let mut alpha = [QM31::ZERO; 10];
    #[cfg(feature = "prover")]
    let mut round_checks = [[QM31::ZERO; 3]; 10];
    {
        let round = 0usize;
        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;
    }
    {
        let round = 1usize;
        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;
    }
    {
        let round = 2usize;
        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;
    }
    {
        let round = 3usize;
        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;
    }
    {
        let round = 4usize;
        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;
    }
    {
        let round = 5usize;
        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;
    }
    {
        let round = 6usize;
        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;
    }
    {
        let round = 7usize;
        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;
    }
    {
        let round = 8usize;
        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;
    }
    {
        let round = 9usize;
        (running, alpha, transcript, round_checks) = semantic_round(prefix, transcript, alpha, running, round, round_checks)?;
    }
    Ok((running, alpha, transcript, round_checks))
}

#[inline(never)]
fn verify_finish<H: Digest32>(public: Public<'_>, prefix: Prefix<'_>, mut transcript: SemanticTranscript<H>, challenges: Challenges, obs: crate::verifier::Observer) -> Result<Verified<H>, Error> {
    #[cfg(not(feature = "prover"))]
    let (running, alpha, mut transcript) = semantic_rounds(&prefix, transcript)?;
    #[cfg(feature = "prover")]
    let (running, alpha, mut transcript, round_checks) = semantic_rounds(&prefix, transcript)?;
    mark(obs, 2);
    let claims = claims(&prefix)?;
    let original_challenges = aspis_core::state_only_prefix::r0::Challenges {
        lambda: challenges.lambda,
        chi: challenges.chi,
        theta: challenges.theta,
        zc: challenges.zc,
        mu: challenges.mu,
        eta: challenges.eta,
    };
    let terminal = public
        .terminal_qm31(&claims, &alpha, &original_challenges)
        .map_err(|_| Error::Public)?;
    mark(obs, 3);
    let mask = aspis_core::state_only_hiding::state_only_selected_mask_value(
        &core::array::from_fn(|i| claims[0][i]),
        &core::array::from_fn(|i| claims[0][16 + i]),
        claims[0][27],
        &alpha,
    );
    let extra = prefix.validated_record(25)?.decode_k::<29>(87)?;
    let masked_terminal = mask.add(challenges.eta.mul(terminal)).add(extra[28]);
    if running != masked_terminal {
        return Err(Error::Terminal);
    }
    mark(obs, 4);
    let state_before_z0 = transcript.state();
    let z0 = transcript.circle_validated(prefix.validated_record(25)?)?;
    let before_z1 = prefix.validated_record(26)?.decode_k::<29>(0)?;
    let z1 = transcript.circle_validated(prefix.validated_record(26)?)?;
    mark(obs, 5);
    #[cfg(feature = "prover")]
    {
        for (i, x) in [z0.x, z0.y, z1.x, z1.y].into_iter().enumerate() {
            crate::trace::value(3, i, aspis_core::field::WideExact::from_qm31(x));
        }
        for (i, x) in challenges.with_alphas(&alpha).into_iter().enumerate() {
            crate::trace::value(0, i, x);
        }
        for (i, row) in round_checks.iter().enumerate() {
            for (j, x) in row.iter().enumerate() {
                crate::trace::value(1, 3 * i + j, aspis_core::field::WideExact::from_qm31(*x));
            }
        }
        crate::trace::value(2, 0, aspis_core::field::WideExact::from_qm31(terminal));
        crate::trace::value(
            2,
            1,
            aspis_core::field::WideExact::from_qm31(masked_terminal),
        );
    }
    if z0 == z1 {
        return Err(Error::EqualCirclePoints);
    }
    Ok(Verified {
        roots: [*prefix.c1_root, prefix.payload(2)?.try_into().unwrap()],
        challenges,
        alpha,
        claims,
        extra,
        before_z1,
        state_before_z0,
        z: [z0, z1],
        transcript,
        #[cfg(feature = "prover")]
        round_checks,
        #[cfg(feature = "prover")]
        terminal,
        #[cfg(feature = "prover")]
        masked_terminal,
    })
}

#[inline(never)]
pub fn verify_observed<H: Digest32>(public: Public<'_>, bytes: &[u8], hash: H, obs: crate::verifier::Observer) -> Result<Verified<H>, Error> {
    let prefix = Prefix::parse(bytes)?;
    mark(obs, 0);
    let mut transcript = public_transcript(public, hash, prefix.c1_root)?;
    let challenges = wire::begin(&prefix, &mut transcript)?;
    mark(obs, 1);
    verify_finish(public, prefix, transcript, challenges, obs)
}
