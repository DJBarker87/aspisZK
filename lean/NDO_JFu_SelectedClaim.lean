import NDO_JFu_TerminalSelected
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_SelectedClaim
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_semantic_terminal

theorem stride : POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1=ok 28#usize := by
  unfold POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  have spec : (do let n ← (16#usize+10#usize : Result Usize);n+2#usize) ⦃ out => out.val=28 ⦄ := by
    step* <;> scalar_tac
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  have same : out=28#usize := UScalar.eq_of_val_eq value
  exact same ▸ call

theorem source (claims : Array field.QM31 84#usize) (point column : Usize)
    (hp : point.val<3) (hc : column.val<28) : ∃ q,selected_claim claims point column=ok q := by
  have spec : selected_claim claims point column ⦃ _ => True ⦄ := by
    unfold selected_claim
    rw [stride]
    step* <;> scalar_tac
  obtain ⟨q,call,_⟩ := WP.spec_imp_exists spec
  exact ⟨q,call⟩

#print axioms stride
#print axioms source
end AspisR1.JFu_SelectedClaim
end
