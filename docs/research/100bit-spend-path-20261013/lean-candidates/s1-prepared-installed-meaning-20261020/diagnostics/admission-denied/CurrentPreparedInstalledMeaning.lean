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
end AspisR1ClaimPreparedBridge.InstalledMeaning
