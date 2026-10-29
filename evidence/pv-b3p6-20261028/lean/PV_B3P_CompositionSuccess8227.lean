import PV_B3P_SemanticStagesSuccess227
import PV_B3P_RustOkStages227
import PV_B3P_Resume6Combined
import PV_B3P_CopySuccess227
import PV_B3P_PoseidonSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] valid_public reference_terminal.semantic_packed
  reference_terminal.validate_transition reference_terminal.select_c1_227
  reference_terminal.composition_parts_loop0 reference_copy_terminal.Selectors.boxed_at_point
  reference_terminal.poseidon_selectors reference_poseidon.evaluate_state_only_poseidon_oracle_projected
  reference_copy_terminal.evaluate_with_selectors host_terminal_field.PreparedQm31Multiplier.new
  reference_terminal.composition_parts_loop1 reference_terminal.composition_parts_loop2
  reference_terminal.selected_claim reference_terminal.copy_variant

theorem composition_success8 (p : reference_terminal.SemanticPublic)
    (claims : Array aspis_core.field.QM31 84#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (lambda chi theta : aspis_core.field.QM31) :
    RustOk (reference_terminal.composition_parts (valid_public p) claims point lambda chi theta) := by
  unfold reference_terminal.composition_parts
  rw [digest_field_withdrawal]
  simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte, valid_public_reset,
    public_transition_success, core.result.Result.Insts.CoreOpsTry.branch]
  apply rust_bind
  · apply total_reference_terminal_select_c1_227; scalar_tac
  intro a0
  apply rust_bind
  · apply total_reference_terminal_select_c1_227; scalar_tac
  intro a1
  apply rust_bind
  · apply total_reference_terminal_select_c1_227; scalar_tac
  intro a2
  apply rust_bind
  · apply mask_loop_total; scalar_tac
  intro mask
  apply rust_bind
  · exact boxed_selectors_total point
  intro selectors
  apply rust_bind
  · exact poseidon_selectors_total selectors
  intro sops
  apply rust_bind
  · exact total_reference_poseidon_evaluate_state_only_poseidon_oracle_projected _ _
  intro poseidon
  apply rust_bind
  · exact semantic_success8 (valid_public p) _ selectors
  intro semantic
  rw [selected_h1_column_value]
  apply rust_bind
  · apply selected_claim_total <;> scalar_tac
  intro h1
  apply rust_bind
  · exact copy_variant_total _
  intro variant
  apply rust_bind
  · exact copy_success _ _ _ _ _ _ _
  intro copy
  apply rust_bind
  · exact total_host_terminal_field_PreparedQm31Multiplier_new theta
  intro prepared
  apply rust_lift
  apply rust_bind
  · apply reverse1_total
    simp only [Slice.len,Array.to_slice,semantic.property]
    scalar_tac
  intro composition
  apply rust_lift
  apply rust_bind
  · apply reverse2_total
    simp only [Slice.len,Array.to_slice,poseidon.property]
    scalar_tac
  intro composition1
  rw [selected_g_column_value]
  apply rust_bind
  · apply selected_claim_total <;> scalar_tac
  intro g
  exact rust_ok _

#print axioms composition_success8
end PV_B3P_Success227
