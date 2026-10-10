//! Unproved COST PROBE; instrumented S4 only.
//! End-to-end P1 R0 acceptance. The semantic result is the only opening hook.
use crate::{
    pool_v1::pair_forest_semantic_terminal::r0::Public,
    r0_probe::semantics::{verify_semantics_heap, VerifiedSemantics, VerifiedSemanticsHeap},
};
use alloc::vec::Vec;
use aspis_core::r0_probe::mark;
use aspis_core::{
    field::WideExact,
    r0::{
        domain::FibreIndex,
        merkle,
        transcript::SemanticBoundary,
        verifier,
        wire::{OpeningProof, OpeningView},
        Error as OpeningError,
    },
    r0_probe::onchain,
    state_only_prefix::r0::{self as semantic_wire, Error as SemanticError},
    HashFn,
};

pub const SEMANTIC_BYTES: usize = 12_903;
/// Row 26 belongs to both borrowed views, but occurs only once on the wire.
pub const OPENING_OFFSET: usize = SEMANTIC_BYTES - (5 + 29 * 32);
pub const PROOF_BYTES: usize = OPENING_OFFSET + aspis_core::r0::wire::PROOF_BYTES;

pub use crate::r0::{Error, Phase};
pub mod semantics;

pub struct Proof<'a> {
    pub semantic: &'a [u8],
    pub opening: &'a [u8],
}
impl<'a> Proof<'a> {
    pub fn parse(bytes: &'a [u8]) -> Result<Self, Error> {
        if bytes.len() != PROOF_BYTES {
            return Err(OpeningError::Parse.into());
        }
        Ok(Self {
            semantic: &bytes[..SEMANTIC_BYTES],
            opening: &bytes[OPENING_OFFSET..],
        })
    }
    /// Round-trip validation uses both strict parsers; no unchecked byte copy.
    pub fn encode(&self) -> Result<Vec<u8>, Error> {
        semantic_wire::Prefix::parse(self.semantic)?;
        let opening = OpeningProof::parse(self.opening)?.encode()?;
        if self.semantic[OPENING_OFFSET..] != opening[..SEMANTIC_BYTES - OPENING_OFFSET] {
            return Err(OpeningError::Parse.into());
        }
        let mut out = Vec::new();
        out.try_reserve_exact(PROOF_BYTES)
            .map_err(|_| OpeningError::Allocation)?;
        out.extend_from_slice(&self.semantic[..OPENING_OFFSET]);
        out.extend_from_slice(&opening);
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
    mark("r0:b:+sem.handoff");
    let boundary = semantic_handoff_heap(&checked)?;
    mark("r0:b:-sem.handoff");
    emit(Phase::Semantic);
    mark("r0:b:+prepare.opening_parse");
    let proof = OpeningView::parse(wire.opening)?;
    mark("r0:b:-prepare.opening_parse");
    let prepared = onchain::prepare(hash, &boundary, &proof)?;
    // Both views must replay exactly the same row-25/26 records.
    mark("r0:b:+prepare.handoff_check");
    if prepared.data.z
        != checked.z.map(|z| aspis_core::r0::domain::Point {
            x: WideExact::from_qm31(z.x),
            y: WideExact::from_qm31(z.y),
        })
    {
        return Err(OpeningError::Schedule.into());
    }
    mark("r0:b:-prepare.handoff_check");
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
        onchain::check_v1(&prepared.v1, &proof, u, &opening, i == 0)?;
        emit(Phase::V1(i));
    }
    onchain::check_v2(
        &prepared.data,
        c.kappa,
        c.tau,
        c.alpha,
        &prepared.polynomial,
        &proof,
    )?;
    emit(Phase::V2);
    Ok(prepared.challenges)
}
