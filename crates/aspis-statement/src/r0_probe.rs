//! End-to-end P1 R0 acceptance. The semantic result is the only opening hook.
use crate::{
    pool_v1::pair_forest_semantic_terminal::r0::Public,
    state_only_verify::r0::{verify_semantics_heap, VerifiedSemantics, VerifiedSemanticsHeap},
};
use aspis_core::r0_probe::onchain;
use aspis_core::{
    field::WideExact,
    r0_probe::{
        domain::FibreIndex, merkle, transcript::SemanticBoundary, verifier, wire::OpeningView,
        Error as OpeningError,
    },
    state_only_prefix::r0 as semantic_wire,
    HashFn,
};

pub use crate::r0::{Error, Phase, OPENING_OFFSET, SEMANTIC_BYTES};
#[cfg(not(feature = "r0-probe-c2"))]
pub use crate::r0::{Proof, PROOF_BYTES};
#[cfg(feature = "r0-probe-c2")]
pub const PROOF_BYTES: usize = crate::r0::PROOF_BYTES + aspis_core::r0_probe::relation::BYTES;
#[cfg(feature = "r0-probe-c2")]
pub struct Proof<'a> {
    pub semantic: &'a [u8],
    pub opening: &'a [u8],
    pub relation: &'a [u8],
}
#[cfg(feature = "r0-probe-c2")]
impl<'a> Proof<'a> {
    pub fn parse(bytes: &'a [u8]) -> Result<Self, Error> {
        if bytes.len() != PROOF_BYTES {
            return Err(OpeningError::Parse.into());
        }
        let split = crate::r0::PROOF_BYTES;
        let wire = crate::r0::Proof::parse(&bytes[..split])?;
        for x in bytes[split..].chunks_exact(32) {
            WideExact::from_le_bytes(x).ok_or(OpeningError::NonCanonical)?;
        }
        Ok(Self {
            semantic: wire.semantic,
            opening: wire.opening,
            relation: &bytes[split..],
        })
    }
    pub fn encode(&self) -> Result<alloc::vec::Vec<u8>, Error> {
        let mut out = crate::r0::Proof {
            semantic: self.semantic,
            opening: self.opening,
        }
        .encode()?;
        out.extend_from_slice(self.relation);
        Proof::parse(&out)?;
        Ok(out)
    }
}

/// Called only with the output of successful semantic verification. In
/// particular, neither a proof-supplied boolean nor a caller-supplied point
/// list can enter the end-to-end acceptance path.
pub fn semantic_handoff(checked: &VerifiedSemantics) -> Result<SemanticBoundary, Error> {
    let boundary = SemanticBoundary::from_verified_parts(
        checked.state_before_z0,
        [checked.c1_root, checked.c2_root],
        checked.challenges.with_alphas(&checked.alpha),
        checked.claims,
        true,
    )?;
    let points = semantic_wire::statement_points(&checked.alpha)
        .map(|p| core::array::from_fn(|b| WideExact::from_qm31(p[9 - b])));
    if boundary.points() != points {
        return Err(OpeningError::Semantic.into());
    }
    Ok(boundary)
}

/// Same handoff checks with a directly initialized heap boundary.
#[inline(never)]
fn semantic_handoff_heap(
    checked: &VerifiedSemanticsHeap,
) -> Result<alloc::boxed::Box<SemanticBoundary>, Error> {
    let boundary = SemanticBoundary::boxed_from_verified_parts(
        checked.state_before_z0,
        [checked.c1_root, checked.c2_root],
        &checked.challenges.with_alphas(&checked.alpha),
        &checked.claims,
        true,
    )?;
    let semantic_points = semantic_wire::statement_points(&checked.alpha);
    let opening_points = boundary.points();
    for p in 0..3 {
        for b in 0..10 {
            if opening_points[p][b] != WideExact::from_qm31(semantic_points[p][9 - b]) {
                return Err(OpeningError::Semantic.into());
            }
        }
    }
    Ok(boundary)
}

/// Complete verifier, with an optional passive diagnostic observer. All
/// semantic, canonicality, sampling, authentication, V1 and V2 checks run.
pub fn r0_verify(
    public: Public<'_>,
    bytes: &[u8],
    hash: HashFn,
    trace: Option<fn(Phase)>,
) -> Result<verifier::Challenges, Error> {
    let emit = |p| {
        if let Some(trace) = trace {
            trace(p);
        }
    };
    let wire = Proof::parse(bytes)?;
    emit(Phase::Parsed);
    let checked = verify_semantics_heap(public, wire.semantic, hash)?;
    let boundary = semantic_handoff_heap(&checked)?;
    emit(Phase::Semantic);
    let proof = OpeningView::parse(wire.opening)?;
    let prepared = onchain::prepare(hash, &boundary, &proof)?;
    // Both views must replay exactly the same row-25/26 records.
    if prepared.data.z
        != checked.z.map(|z| aspis_core::r0::domain::Point {
            x: WideExact::from_qm31(z.x),
            y: WideExact::from_qm31(z.y),
        })
    {
        return Err(OpeningError::Schedule.into());
    }
    emit(Phase::ChordClaims);
    let c = &prepared.challenges;
    for (i, u) in c.queries.sorted().into_iter().enumerate() {
        let opening = proof.fibre(i);
        let u = FibreIndex::new(u as usize)?;
        if !merkle::verify_pair(
            hash,
            &prepared.data.roots,
            u,
            opening.leaf_hashes(hash)?,
            opening.paths(),
        ) {
            return Err(OpeningError::Authentication.into());
        }
        emit(Phase::Merkle(i));
        onchain::check_v1(&prepared.v1, &proof, u, &opening)?;
        emit(Phase::V1(i));
    }
    #[cfg(any(not(feature = "r0-probe-c2"), feature = "r0-probe-reference"))]
    let direct = onchain::check_v2(
        &prepared.data,
        c.kappa,
        c.tau,
        c.alpha,
        &prepared.polynomial,
        &proof,
    );
    #[cfg(not(feature = "r0-probe-c2"))]
    direct?;
    #[cfg(all(feature = "r0-probe-c2", feature = "r0-probe-reference"))]
    let _ = direct;
    #[cfg(feature = "r0-probe-c2")]
    aspis_core::r0_probe::relation::verify(
        hash,
        prepared.relation_state,
        &prepared.data,
        c.kappa,
        c.tau,
        c.alpha,
        &prepared.polynomial,
        &proof,
        wire.relation,
    )?;
    emit(Phase::V2);
    Ok(prepared.challenges)
}

/// Native differential reference at the R-E3 base.
#[cfg(all(feature = "r0-probe-reference", not(target_os = "solana")))]
pub fn r0_verify_re3(
    public: Public<'_>,
    bytes: &[u8],
    hash: HashFn,
    trace: Option<fn(Phase)>,
) -> Result<verifier::Challenges, Error> {
    let _reference = aspis_core::r0_probe::equality_trace::reference();
    let emit = |p| {
        if let Some(trace) = trace {
            trace(p);
        }
    };
    let wire = Proof::parse(bytes)?;
    emit(Phase::Parsed);
    let checked = verify_semantics_heap(public, wire.semantic, hash)?;
    let boundary = semantic_handoff_heap(&checked)?;
    emit(Phase::Semantic);
    let proof = OpeningView::parse(wire.opening)?;
    let prepared = aspis_core::r0_probe::onchain_re3::prepare(hash, &boundary, &proof)?;
    // Both views must replay exactly the same row-25/26 records.
    if prepared.data.z
        != checked.z.map(|z| aspis_core::r0::domain::Point {
            x: WideExact::from_qm31(z.x),
            y: WideExact::from_qm31(z.y),
        })
    {
        return Err(OpeningError::Schedule.into());
    }
    emit(Phase::ChordClaims);
    let c = &prepared.challenges;
    for (i, u) in c.queries.sorted().into_iter().enumerate() {
        let opening = proof.fibre(i);
        let u = FibreIndex::new(u as usize)?;
        if !merkle::verify_pair(
            hash,
            &prepared.data.roots,
            u,
            opening.leaf_hashes(hash)?,
            opening.paths(),
        ) {
            return Err(OpeningError::Authentication.into());
        }
        emit(Phase::Merkle(i));
        aspis_core::r0_probe::onchain_re3::check_v1(&prepared.v1, &proof, u, &opening)?;
        emit(Phase::V1(i));
    }
    aspis_core::r0_probe::onchain_re3::check_v2(
        &prepared.data,
        c.kappa,
        c.tau,
        c.alpha,
        &prepared.polynomial,
        &proof,
    )?;
    #[cfg(feature = "r0-probe-c2")]
    aspis_core::r0_probe::relation::verify(
        hash,
        prepared.relation_state,
        &prepared.data,
        c.kappa,
        c.tau,
        c.alpha,
        &prepared.polynomial,
        &proof,
        wire.relation,
    )?;
    emit(Phase::V2);
    Ok(prepared.challenges)
}
