//! Unproved COST PROBE; isolated S4 semantics.
use crate::pool_v1::pair_forest_semantic_terminal::r0::Public;
use aspis_core::circle::SecureCirclePoint;
use aspis_core::field::{WideExact, QM31};
use aspis_core::r0_probe::mark;
use aspis_core::r0_probe::prefix::{
    self as wire, Challenges, Error, PointClaims, Prefix, SemanticTranscript,
};
use aspis_core::r0_probe::sumcheck;
use aspis_core::state_only_hiding::r0::masked_terminal;
use aspis_core::transcript::HashFn;

pub struct VerifiedSemantics {
    pub c1_root: [u8; 32],
    pub c2_root: [u8; 32],
    pub challenges: Challenges,
    pub alpha: [QM31; 10],
    pub claims: PointClaims,
    pub before_z1: [WideExact; 29],
    /// Pass this state, both roots, challenges.with_alphas(&alpha), and
    /// claims to R-D's SemanticBoundary::from_verified_parts. R-D replays
    /// rows 25/26 itself; passing the row-27 state would double-absorb.
    pub state_before_z0: [u8; 32],
    pub z: [SecureCirclePoint; 2],
    /// State immediately before opening row 27. No extra gamma, delta,
    /// OOD mixing, statement-point or work-nonce absorbs/squeezes.
    pub transcript: SemanticTranscript,
}
pub fn verify_semantics(
    public: Public<'_>,
    bytes: &[u8],
    hash: HashFn,
) -> Result<VerifiedSemantics, Error> {
    let prefix = Prefix::parse(bytes)?;
    let mut transcript = SemanticTranscript::new(hash, &public.public_bytes()?, prefix.c1_root)?;
    let challenges = wire::begin(&prefix, &mut transcript)?;
    let checked = sumcheck::verify(&prefix, &mut transcript)?;
    let claims = prefix.point_claims()?;
    let terminal = public.terminal(&claims, &checked.alpha, &challenges)?;
    if checked.terminal_claim != masked_terminal(&claims, &checked.alpha, challenges.eta, terminal)
    {
        return Err(Error::Terminal);
    }
    let state_before_z0 = transcript.state();
    let z0 = transcript.challenge_reference_circle_point(25, prefix.record(25)?)?;
    let before_z1 = wire::decode_values::<29>(26, prefix.payload(26)?)?;
    let z1 = transcript.challenge_reference_circle_point(26, prefix.record(26)?)?;
    if z0 == z1 {
        return Err(Error::EqualCirclePoints);
    }
    // Retain beforeZ1 literally. The model does not compare this message
    // to the repeated Y0 in row 27; that record belongs to R-D.
    Ok(VerifiedSemantics {
        c1_root: *prefix.c1_root,
        c2_root: prefix.payload(2)?.try_into().unwrap(),
        challenges,
        alpha: checked.alpha,
        claims,
        before_z1,
        state_before_z0,
        z: [z0, z1],
        transcript,
    })
}
// Representation-only verifier variant. The checks and their sequence
// deliberately match verify_semantics above.
pub struct VerifiedSemanticsHeap {
    pub c1_root: [u8; 32],
    pub c2_root: [u8; 32],
    pub challenges: Challenges,
    pub alpha: [QM31; 10],
    pub claims: alloc::boxed::Box<PointClaims>,
    pub before_z1: alloc::boxed::Box<[WideExact; 29]>,
    /// Pass this state, both roots, challenges.with_alphas(&alpha), and
    /// claims to R-D's SemanticBoundary::from_verified_parts. R-D replays
    /// rows 25/26 itself; passing the row-27 state would double-absorb.
    pub state_before_z0: [u8; 32],
    pub z: [SecureCirclePoint; 2],
    /// State immediately before opening row 27. No extra gamma, delta,
    /// OOD mixing, statement-point or work-nonce absorbs/squeezes.
    pub transcript: SemanticTranscript,
}
#[inline(never)]
fn before_z1_heap(payload: &[u8]) -> Result<alloc::boxed::Box<[WideExact; 29]>, Error> {
    let mut out =
        aspis_core::r0::heap::uninit::<[WideExact; 29]>().map_err(|_| Error::Allocation)?;
    // The same decoder and canonicality checks, with only storage changed.
    out.write(wire::decode_values::<29>(26, payload)?);
    Ok(unsafe { out.assume_init() })
}
#[inline(never)]
pub fn verify_semantics_heap(
    public: Public<'_>,
    bytes: &[u8],
    hash: HashFn,
) -> Result<VerifiedSemanticsHeap, Error> {
    mark("r0:b:+sem.parse_canonical");
    let prefix = Prefix::parse(bytes)?;
    mark("r0:b:-sem.parse_canonical");
    mark("r0:b:+sem.public_transcript_init");
    let mut transcript = SemanticTranscript::new(hash, &public.public_bytes()?, prefix.c1_root)?;
    mark("r0:b:-sem.public_transcript_init");
    mark("r0:b:+sem.begin");
    let challenges = wire::begin(&prefix, &mut transcript)?;
    mark("r0:b:-sem.begin");
    mark("r0:b:+sem.sumcheck");
    let checked = sumcheck::verify(&prefix, &mut transcript)?;
    mark("r0:b:-sem.sumcheck");
    mark("r0:b:+sem.point_claims");
    let claims = prefix.point_claims_boxed()?;
    mark("r0:b:-sem.point_claims");
    mark("r0:b:+sem.terminal_mask");
    let terminal = public.terminal(&claims, &checked.alpha, &challenges)?;
    if checked.terminal_claim != masked_terminal(&claims, &checked.alpha, challenges.eta, terminal)
    {
        return Err(Error::Terminal);
    }
    mark("r0:b:-sem.terminal_mask");
    mark("r0:b:+sem.extra_claims_points");
    let state_before_z0 = transcript.state();
    let z0 = transcript.challenge_reference_circle_point(25, prefix.record(25)?)?;
    let before_z1 = before_z1_heap(prefix.payload(26)?)?;
    let z1 = transcript.challenge_reference_circle_point(26, prefix.record(26)?)?;
    if z0 == z1 {
        return Err(Error::EqualCirclePoints);
    }
    mark("r0:b:-sem.extra_claims_points");
    // Retain beforeZ1 literally. The model does not compare this message
    // to the repeated Y0 in row 27; that record belongs to R-D.
    Ok(VerifiedSemanticsHeap {
        c1_root: *prefix.c1_root,
        c2_root: prefix.payload(2)?.try_into().unwrap(),
        challenges,
        alpha: checked.alpha,
        claims,
        before_z1,
        state_before_z0,
        z: [z0, z1],
        transcript,
    })
}
