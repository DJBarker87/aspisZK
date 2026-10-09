//! SPEC §8 Accept after the trusted semantic hook: parse, reconstruct,
//! authenticate/V1 per sampled fibre, then V2. no_std + alloc.
use super::{
    basis::NaturalBasis,
    domain::{self, FibreIndex, SlotIndex},
    encoder, fold, merkle,
    opening::{self, OpeningData},
    transcript::{OpeningTranscript, QuerySet, SemanticBoundary},
    wire::{FibreOpening, OpeningProof},
    Error,
};
use crate::{field::WideExact as E, HashFn};
#[derive(Clone, Debug)]
pub struct Challenges {
    pub gamma: E,
    pub kappa: E,
    pub tau: E,
    pub alpha: E,
    pub queries: QuerySet,
}
pub struct Prepared {
    pub data: OpeningData,
    pub challenges: Challenges,
    pub polynomial: [E; 7],
    pub transcript_state: [u8; 32],
}
/// Derive every challenge from parsed records; no caller-supplied S or γ.
pub fn prepare(
    hash: HashFn,
    boundary: &SemanticBoundary,
    proof: &OpeningProof,
) -> Result<Prepared, Error> {
    if proof.openings.len() != 22 {
        return Err(Error::Parse);
    }
    let mut t = OpeningTranscript::new(hash, boundary);
    let z0 = t.z0(&boundary.claims)?;
    let z1 = t.z1(&proof.y0)?;
    let data = OpeningData {
        roots: boundary.roots(),
        z: [z0, z1],
        y: proof.y,
        points: boundary.points(),
        claims: boundary.claims,
    };
    data.validate_points()?;
    let gamma = t.gamma(&proof.y)?;
    let kappa = t.kappa(proof.v)?;
    let tau = t.tau()?;
    let [c0, c1, c2, c3, c5, c6] = proof.coefficients;
    let c4 = fold::quarter::<E>()
        .mul(data.claim_prime(gamma, proof.v, kappa)?)
        .sub(c0);
    let polynomial = [c0, c1, c2, c3, c4, c5, c6];
    let alpha = t.alpha(&polynomial)?;
    let queries = t.queries(&proof.final_message)?;
    Ok(Prepared {
        data,
        challenges: Challenges {
            gamma,
            kappa,
            tau,
            alpha,
            queries,
        },
        polynomial,
        transcript_state: t.state(),
    })
}
/// Algebraic V1 at one authenticated fibre; kept separate for diagnostic
/// tests. This helper alone is not an authentication/acceptance API.
pub fn check_v1(
    data: &OpeningData,
    gamma: E,
    alpha: E,
    f: &super::FinalMessage<E>,
    u: FibreIndex,
    opening: &FibreOpening,
) -> Result<(), Error> {
    let g = opening::powers::<29>(gamma);
    let i = data.interpolant_batch(gamma)?;
    let line = data.line();
    let mut r = [E::ZERO; 4];
    for s in 0..4 {
        let index = domain::child_index(u, SlotIndex::new(s)?);
        let numerator =
            opening::dot(&g, &opening.values[s]).sub(encoder::exact_initial_encoder(&i, index));
        r[s] = numerator.mul(
            line.line_word(index)
                .try_inv()
                .ok_or(Error::ZeroDenominator)?,
        );
    }
    if fold::fold_fibre(alpha, u, r)? != encoder::exact_final_encoder(f, u) {
        return Err(Error::V1);
    }
    Ok(())
}
pub fn check_v2(
    basis: &NaturalBasis,
    data: &OpeningData,
    kappa: E,
    tau: E,
    alpha: E,
    c: &[E; 7],
    f: &super::FinalMessage<E>,
) -> Result<(), Error> {
    let lhs = c.iter().rev().fold(E::ZERO, |v, &c| v.mul(alpha).add(c));
    let rhs = fold::quarter::<E>().mul(opening::dot(
        f,
        &fold::dual_fold(alpha, &data.total_weights(basis, kappa, tau)?),
    ));
    if lhs != rhs {
        return Err(Error::V2);
    }
    Ok(())
}
pub fn verify(
    hash: HashFn,
    basis: &NaturalBasis,
    boundary: &SemanticBoundary,
    bytes: &[u8],
) -> Result<Challenges, Error> {
    let proof = OpeningProof::parse(bytes)?;
    let p = prepare(hash, boundary, &proof)?;
    let c = &p.challenges;
    for (u, opening) in c.queries.sorted().into_iter().zip(&proof.openings) {
        let u = FibreIndex::new(u as usize)?;
        if !merkle::verify_pair(
            hash,
            &p.data.roots,
            u,
            opening.leaf_hashes(hash)?,
            &opening.paths,
        ) {
            return Err(Error::Authentication);
        }
        check_v1(&p.data, c.gamma, c.alpha, &proof.final_message, u, opening)?;
    }
    check_v2(
        basis,
        &p.data,
        c.kappa,
        c.tau,
        c.alpha,
        &p.polynomial,
        &proof.final_message,
    )?;
    Ok(p.challenges)
}
