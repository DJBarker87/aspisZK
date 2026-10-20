import CurrentPreparedConcreteRun
import CurrentClaimPowerReads
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim AspisR1CurrentPreparedClaim.Concrete

theorem prepared_success_scratch_meaning {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch scratchIn : Array PE 29#usize)
    (hgamma : Canonical (toClaimE out.gamma))
    (h : AspisR1PublicPreparation.PreparedScratchModel.prepare
      (concreteBoundaries sampling) D sem v hash scratchIn=ok (.Ok out,scratch)) :
    ∀ i : Usize, i.val<29 → ∃ value : E,
      Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
      Canonical value ∧ decode value=decode (toClaimE out.gamma)^i.val := by
  have hr := prepared_success_concrete_claim sampling D sem v hash out scratch scratchIn h
  intro i hi
  have hib : i.val<(mapArray toClaimE scratch).val.length := by
    simpa only [(mapArray toClaimE scratch).property] using hi
  obtain ⟨value,hread,hcell⟩ := WP.spec_imp_exists
    (Array.index_usize_spec (mapArray toClaimE scratch) i hib)
  exact ⟨value,hread,ClaimPowers.powers_success_read (toClaimE out.gamma)
    (mapArray toClaimE scratch) hgamma hr.1 i value hread⟩

#print axioms prepared_success_scratch_meaning
end AspisR1ClaimPreparedBridge
