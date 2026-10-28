import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
noncomputable section
namespace NBD_DigestInduction
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder
attribute [local instance] Classical.propDecidable

def Canonical (d : Array U32 8#usize) : Prop :=
  ∀ j : Fin 8, (d.val[j.val]'(by have := d.property; scalar_tac)).val < 2147483647

def Suffix (d : Array U32 8#usize) (i : Nat) : Prop :=
  ∀ j : Fin 8, i ≤ j.val → (d.val[j.val]'(by have := d.property; scalar_tac)).val < 2147483647

/-- The two native digest scanners have identical emitted bodies, including rejection. -/
theorem same_scanner (d : Array U32 8#usize) :
    pool_v1.pair_forest_accounts.digest_is_canonical d =
    pool_v1.pair_tree_profile.digest_is_canonical d := by
  unfold pool_v1.pair_forest_accounts.digest_is_canonical
    pool_v1.pair_tree_profile.digest_is_canonical
    pool_v1.pair_forest_accounts.digest_is_canonical_loop
    pool_v1.pair_tree_profile.digest_is_canonical_loop
    pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    pool_v1.pair_tree_profile.digest_is_canonical_loop.body
  rfl

/-- Full Boolean result, with no canonicality precondition. -/
theorem source (d : Array U32 8#usize) :
    pool_v1.pair_tree_profile.digest_is_canonical d = ok (decide (Canonical d)) := by
  have spec : pool_v1.pair_tree_profile.digest_is_canonical d
      ⦃ b => b = decide (Canonical d) ⦄ := by
    unfold pool_v1.pair_tree_profile.digest_is_canonical
      pool_v1.pair_tree_profile.digest_is_canonical_loop
    refine loop.spec_decr_nat (fun i : Usize => 8-i.val)
      (fun i : Usize => i.val ≤ 8 ∧ (Canonical d ↔ Suffix d i.val))
      (fun b : Bool => b = decide (Canonical d))
      (fun i => pool_v1.pair_tree_profile.digest_is_canonical_loop.body d i) 0#usize ?_ ?_
    · intro i hi
      rcases hi with ⟨bound,eqv⟩
      unfold pool_v1.pair_tree_profile.digest_is_canonical_loop.body
      step*
      all_goals try unfold aspis_core.field.P at *
      all_goals simp_all [Canonical, Suffix]
      all_goals first | scalar_tac | skip
      · refine ⟨⟨i.val, by scalar_tac⟩, Nat.le_refl _, ?_⟩
        assumption
      · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        constructor
        · intro h j hj
          exact h j (by omega)
        · intro h j hj
          by_cases same : j.val = i.val
          · simpa only [same] using (show (d.val[i.val]'(by have := d.property; scalar_tac)).val < 2147483647 from by assumption)
          · exact h j (by omega)
    · constructor
      · scalar_tac
      · simp [Canonical, Suffix]
  obtain ⟨b,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms same_scanner
#print axioms source
end NBD_DigestInduction
