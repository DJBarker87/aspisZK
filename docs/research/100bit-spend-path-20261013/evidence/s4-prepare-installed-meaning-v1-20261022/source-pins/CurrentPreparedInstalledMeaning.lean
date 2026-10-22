import CurrentPreparedSourceFromQm
import CurrentPreparedAlphaCanonical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete
open AspisR1PublicPreparation
open PreparedFromQmSourceBridge

def installedBoundaries (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact) : PreparedModel.Boundaries :=
  withSourceFromQm (CurrentQueryRho.withConcreteQueries (withCandidateSamplers sampling) embed)

theorem installed_as_candidate_samplers (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact) :
    installedBoundaries sampling embed =
      withCandidateSamplers (withSourceFromQm (CurrentQueryRho.withConcreteQueries sampling embed)) := rfl

theorem installed_as_concrete_queries (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact) :
    installedBoundaries sampling embed =
      CurrentQueryRho.withConcreteQueries (withSourceFromQm (withCandidateSamplers sampling)) embed := rfl

theorem prepared_installed_meaning {H : Type}
    (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (out : verifier.Prepared)
    (scratch scratchIn : Array PE 29#usize)
    (hinactive : Canonical (toClaimE v.inactive))
    (h : PreparedScratchModel.prepare
      (AspisR1ClaimPreparedBridge.concreteBoundaries (installedBoundaries sampling embed))
      D sem v hash scratchIn=ok (.Ok out,scratch)) :
    (Canonical (toClaimE out.gamma) ∧ Canonical (toClaimE out.kappa)) ∧
    CanonicalAlphaPair out ∧
    OriginalPayloadClaimMeaning sem v.y1 (toClaimE v.inactive)
      (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim)
      (mapArray toClaimE scratch) ∧
    (∀ i : Usize, i.val<29 → ∃ value : E,
      Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
      Canonical value ∧ decode value=decode (toClaimE out.gamma)^i.val) := by
  rw [installed_as_candidate_samplers] at h
  let base := withSourceFromQm (CurrentQueryRho.withConcreteQueries sampling embed)
  exact ⟨prepared_candidate_samplers_canonical base D sem v hash out scratch scratchIn h,
    prepared_candidate_alpha_pair base D sem v hash out scratch scratchIn h,
    prepared_candidate_samplers_original_payload base D sem v hash out scratch scratchIn hinactive h,
    prepared_candidate_samplers_scratch base D sem v hash out scratch scratchIn h⟩

#print axioms installed_as_candidate_samplers
#print axioms installed_as_concrete_queries
#print axioms prepared_installed_meaning

open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
open AspisR1.QuerySampler AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1Query31Transcript AspisV8R19.Q22WordScan
open Query31ModelDriverChain Query31ExplicitListLoop Query31ModelScanCall
open Query31ConcreteMaterializedSchedule Query31ConcreteDriverTraceFacts
open Query31ConcreteMaterializedScheduleFull CurrentQueryRho

theorem prepared_installed_query_rho {H M Cv : Type} {L : Nat}
    (sampling : PreparedModel.Boundaries)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (out : verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : PreparedScratchModel.prepare
      (AspisR1ClaimPreparedBridge.concreteBoundaries (installedBoundaries sampling embed))
      D sem v hash scratchIn=ok (.Ok out,scratch)) :
    ∃ (row : U8) (before afterQueries last : transcript.Transcript H) (block : Array U8 32#usize),
      (row=30#u8 ∨ row=31#u8) ∧
      QueriesModel.queries (Query31ConcreteMaterializedSchedule.concreteBoundaries sourceDefaultState embed)
        D before row v.final_message=ok (.Ok out.queries,afterQueries) ∧
      QueryScheduleFacts D p pubInput root length before afterQueries row v.final_message out.queries ∧
      transcript.Transcript.block D afterQueries (if row=30#u8 then 31#u8 else 32#u8)
        PreparedScratchReachability.emptyPayload=ok (block,last) ∧
      sampler.qm31_sample block=ok out.rho ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld out.rho)) ∧
      AspisR1.ExtractedQM31SamplerCorrect.coordinates (SamplerTransport.toOld out.rho)=
        AspisR1.SamplerNatModel.qm31Digits (AspisR1.SourceSamplerByteRank.rank block) ∧
      out.state=last.state := by
  rw [installed_as_concrete_queries] at h
  exact CurrentQueryRho.prepared_success_concrete_query_rho
    (withSourceFromQm (withCandidateSamplers sampling)) D p pubInput root length
    sem v hash embed out scratch scratchIn h

#print axioms prepared_installed_query_rho
end AspisR1ClaimPreparedBridge.InstalledMeaning
