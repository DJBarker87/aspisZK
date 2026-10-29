import NED_ScannerCohorts
import NBH_Frontier
set_option autoImplicit false
noncomputable section
namespace NED_RawAfterFrontier
open Aeneas Aeneas.Std Result WP AspisR1AdapterReconstruct
open NBD_DigestInduction NBH_Frontier
attribute [local instance] Classical.propDecidable

theorem afterstate_loop (a : Frontier) :
    aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate_loop a 0#usize =
    ok (if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalAfterstate) := by
  have spec : aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate_loop a 0#usize
      ⦃ r => r = if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalAfterstate ⦄ := by
    unfold aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate_loop
    refine loop.spec_decr_nat (fun i : Usize => 20-i.val)
      (fun i : Usize => i.val ≤ 20 ∧ (CanonicalFrom a 0 ↔ CanonicalFrom a i.val))
      (fun r => r = if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalAfterstate)
      (fun i => aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate_loop.body a i) 0#usize ?_ ?_
    · intro i hi
      rcases hi with ⟨bound,eqv⟩
      unfold aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate_loop.body
      simp only [NED_ScannerCohorts.profile_result]
      step*
      all_goals simp_all [CanonicalFrom]
      all_goals first | scalar_tac | skip
      · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        constructor
        · intro h j hj; exact h j (by omega)
        · intro h j hj
          by_cases same : j.val = i.val
          · simpa only [same] using (show Canonical (a.val[i.val]'(by have := a.property; scalar_tac)) from by assumption)
          · exact h j (by omega)
      · refine ⟨⟨i.val, by scalar_tac⟩, Nat.le_refl _, ?_⟩
        assumption
    · exact ⟨by scalar_tac, Iff.rfl⟩
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms afterstate_loop
end NED_RawAfterFrontier
