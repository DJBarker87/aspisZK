import PreparedSourcePowersBoundariesV1
import PreparedSourcePowersMeaningV1
import CurrentPreparedJointRankMeaning
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1PreparedSourcePowersJointRankV1
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1PublicPreparation AspisR1CurrentPreparedClaim.Concrete
open PreparedFromQmSourceBridge AspisR1Post25SamplerOrdinaryRankV1
open AspisR1PreparedSourcePowersBoundariesV1 AspisR1PreparedSourcePowersMeaningV1
local notation "ordinaryBoundary" => AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary

/-- Actual returned transcript links and rank witnesses for preparation using
the source powers array interface. No inactive canonicality premise is needed
for the transcript statement. Both fold paths use the same successful run. -/
theorem prepared_sourcePowers_joint_rank_trace {H M Cv : Type} {L : Nat}
    (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (out : verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : PreparedScratchModel.prepare (sourceBoundaries (installedBoundaries sampling embed))
      D sem v hash scratchIn=ok (.Ok out,scratch)) :
    JointRankTrace sampling embed D p pubInput root length sem v hash out scratch := by
  obtain ⟨start,t1,t2,t3,bytes,gamma,kappa,alpha0,hseed,hg,hb,hk,ha,ht⟩ :=
    PreparedScratchReachability.prepare_success
      (sourceBoundaries (installedBoundaries sampling embed)) D sem v hash out scratch scratchIn h
  let base := withSourceFromQm (CurrentQueryRho.withConcreteQueries sampling embed)
  change PreparedModel.scalar (withCandidateGamma (ordinaryBoundary base))
    D start 27#u8 v.y1 true=ok (gamma,t1) at hg
  change PreparedModel.scalar (ordinaryBoundary (withCandidateGamma base))
    D t1 28#u8 (Array.to_slice bytes) false=ok (kappa,t2) at hk
  change PreparedModel.scalar (ordinaryBoundary (withCandidateGamma base))
    D t2 29#u8 v.round0 false=ok (alpha0,t3) at ha
  have hgc := scalar_candidate_gamma_canonical (ordinaryBoundary base)
    D start t1 27#u8 v.y1 gamma hg
  have hkc := AspisR1Post25SamplerOrdinaryCallbackV2.scalar_candidate_ordinary_canonical
    (withCandidateGamma base) D t1 t2 28#u8 (Array.to_slice bytes) kappa hk
  have htail := sourceTail_transport (installedBoundaries sampling embed) D sem v
    gamma kappa alpha0 t3 out scratch hgc hkc ht
  have fields := tail_concrete_run (installedBoundaries sampling embed)
    D sem v gamma kappa alpha0 t3 out scratch htail
  obtain ⟨gb,hgb,hrg⟩ := scalar_candidate_gamma_rank (ordinaryBoundary base)
    D start t1 27#u8 v.y1 gamma hg
  obtain ⟨kb,hkb,hrk⟩ := scalar_candidate_ordinary_rank (withCandidateGamma base)
    D t1 t2 28#u8 (Array.to_slice bytes) kappa hk
  obtain ⟨ab,hab,hra⟩ := scalar_candidate_ordinary_rank (withCandidateGamma base)
    D t2 t3 29#u8 v.round0 alpha0 ha
  refine ⟨start,t1,t2,t3,bytes,alpha0,gb,kb,ab,hseed,hb,hgb,?_,hkb,?_,hab,hra,?_⟩
  · simpa only [fields.1] using hrg
  · simpa only [fields.2.1] using hrk
  · exact tail_ranked_facts sampling embed D p pubInput root length sem v
      gamma kappa alpha0 t3 out scratch htail

/-- The source claim equation and the joint challenge/query/rho rank trace
are consequences of the SAME successful preparation, not separate witnesses. -/
theorem prepared_sourcePowers_claim_and_rank {H M Cv : Type} {L : Nat}
    (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (out : verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (hinactive : Canonical (toClaimE v.inactive))
    (h : PreparedScratchModel.prepare (sourceBoundaries (installedBoundaries sampling embed))
      D sem v hash scratchIn=ok (.Ok out,scratch)) :
    ((Canonical (toClaimE out.gamma) ∧ Canonical (toClaimE out.kappa)) ∧
      ClaimSourceMeaning (toClaimSem sem) v.y1 (toClaimE v.inactive)
        (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim) (mapArray toClaimE scratch)) ∧
    JointRankTrace sampling embed D p pubInput root length sem v hash out scratch := by
  have hc := h
  rw [installed_as_candidate_samplers] at hc
  exact ⟨prepared_sourcePowers_claim_meaning _ D sem v hash out scratch scratchIn hinactive hc,
    prepared_sourcePowers_joint_rank_trace sampling embed D p pubInput root length
      sem v hash out scratch scratchIn h⟩

#print axioms prepared_sourcePowers_joint_rank_trace
#print axioms prepared_sourcePowers_claim_and_rank
end AspisR1PreparedSourcePowersJointRankV1
