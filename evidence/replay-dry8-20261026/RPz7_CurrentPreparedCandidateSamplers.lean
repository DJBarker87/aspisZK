import RPz7_CurrentPreparedGammaRank
import RPz7_CurrentSamplerOrdinaryCallbackV2
import RPz7_CurrentPreparedScratchMeaning
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim.Concrete
local notation "ordinaryBoundary" => AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary

def withCandidateSamplers (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    AspisR1PublicPreparation.PreparedModel.Boundaries :=
  withCandidateGamma (ordinaryBoundary sampling)

theorem candidate_sampler_updates_commute
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    withCandidateSamplers sampling=ordinaryBoundary (withCandidateGamma sampling) := rfl

theorem prepared_candidate_samplers_canonical {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries (withCandidateSamplers sampling)) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    Canonical (toClaimE out.gamma) ∧ Canonical (toClaimE out.kappa) := by
  refine ⟨prepared_candidate_gamma_canonical (ordinaryBoundary sampling) D sem v hash out scratch scratchIn h,?_⟩
  have ho := h
  rw [candidate_sampler_updates_commute] at ho
  exact AspisR1Post25SamplerOrdinaryCallbackV2.prepared_candidate_ordinary_kappa_canonical
    (withCandidateGamma sampling) D sem v hash out scratch scratchIn ho

theorem prepared_candidate_samplers_original_payload {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (hinactive : Canonical (toClaimE v.inactive))
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries (withCandidateSamplers sampling)) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    OriginalPayloadClaimMeaning sem v.y1 (toClaimE v.inactive)
      (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim)
      (mapArray toClaimE scratch) := by
  have hc := prepared_candidate_samplers_canonical sampling D sem v hash out scratch scratchIn h
  exact prepared_success_original_payload_claim (withCandidateSamplers sampling) D sem v hash
    out scratch scratchIn hc.1 hc.2 hinactive h

theorem prepared_candidate_samplers_scratch {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries (withCandidateSamplers sampling)) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    ∀ i : Usize, i.val<29 → ∃ value : E,
      Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
      Canonical value ∧ decode value=decode (toClaimE out.gamma)^i.val := by
  exact prepared_success_scratch_meaning (withCandidateSamplers sampling) D sem v hash out scratch scratchIn
    (prepared_candidate_samplers_canonical sampling D sem v hash out scratch scratchIn h).1 h

#print axioms candidate_sampler_updates_commute
#print axioms prepared_candidate_samplers_canonical
#print axioms prepared_candidate_samplers_original_payload
#print axioms prepared_candidate_samplers_scratch
end AspisR1ClaimPreparedBridge
