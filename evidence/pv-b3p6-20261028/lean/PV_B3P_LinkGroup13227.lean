import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Groups13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227
set_option autoImplicit false
universe u
abbrev Slot13 {α : Sort u} (_target : α) := α
noncomputable section
structure ChangedBodies13 where
  body0 : Slot13 (@reference_terminal.absorption_lanes_literal)
  body1 : Slot13 (@reference_terminal.add_digest_binding)
  body2 : Slot13 (@reference_terminal.add_path_lanes)
  body3 : Slot13 (@reference_terminal.add_preweighted)
  body4 : Slot13 (@reference_terminal.add_schedule_lanes)
  body5 : Slot13 (@reference_terminal.add_value_lanes)
  body6 : Slot13 (@reference_terminal.composition_parts)
  body7 : Slot13 (@reference_terminal.equality_value)
  body8 : Slot13 (@reference_terminal.occupancy_lanes_literal)
  body9 : Slot13 (@reference_terminal.path_lanes_literal)
  body10 : Slot13 (@reference_terminal.poseidon_selectors)
  body11 : Slot13 (@reference_terminal.public_digest_lanes)
  body12 : Slot13 (@reference_terminal.reconstruct_10)
  body13 : Slot13 (@reference_terminal.semantic_initial_and_absorption)
  body14 : Slot13 (@reference_terminal.semantic_packed)
  body15 : Slot13 (fun (selectors : reference_copy_terminal.Selectors) ranges => sum_ranges_reference13 selectors.high ranges aspis_core.field.QM31.ZERO)
  body16 : Slot13 (@reference_terminal.validate_transition)
  body17 : Slot13 (@reference_copy_terminal.Selectors.active_literal)
  body18 : Slot13 (@reference_copy_terminal.pattern_values_literal)
  body19 : Slot13 (@reference_copy_terminal.selector_mask_sum_16)
  body20 : Slot13 (@reference_field.qm31_m31_dot)
  body21 : Slot13 (@reference_field.qm31_sum_products3_prepared)
  body22 : Slot13 (@selector_reference13)
  body23 : Slot13 (@reference_poseidon.evaluate_state_only_poseidon_oracle_projected)
  body24 : Slot13 (@reference_copy_terminal.Selectors.expand)
  body25 : Slot13 (@reference_poseidon.external_linear_lazy)
  body26 : Slot13 (@reference_poseidon.external_linear_packed)
  body27 : Slot13 (@reference_poseidon.external_local_packed_raw)
  body28 : Slot13 (@reference_poseidon.full_round)
  body29 : Slot13 (@reference_poseidon.full_round_m31_constants)
  body30 : Slot13 (@reference_poseidon.full_round_m31_constants_packed)
  body31 : Slot13 (@reference_poseidon.full_round_packed)
  body32 : Slot13 (@reference_poseidon.internal_linear_lazy)
  body33 : Slot13 (@reference_poseidon.interpolate_three_constant_columns)
  body34 : Slot13 (@reference_poseidon.interpolated_internal_pair)
  body35 : Slot13 (@reference_poseidon.leading_pair_packed)

def PV_B3P_Link_changed_bodies (source : ChangedBodies13) : Prop :=
  PV_B3P_Link_terminal_absorption_lanes_literal source.body0 ∧
  PV_B3P_Link_terminal_add_digest_binding source.body1 ∧
  PV_B3P_Link_terminal_add_path_lanes source.body2 ∧
  PV_B3P_Link_terminal_add_preweighted source.body3 ∧
  PV_B3P_Link_terminal_add_schedule_lanes source.body4 ∧
  PV_B3P_Link_terminal_add_value_lanes source.body5 ∧
  PV_B3P_Link_terminal_composition_parts source.body6 ∧
  PV_B3P_Link_terminal_equality_value source.body7 ∧
  PV_B3P_Link_terminal_occupancy_lanes_literal source.body8 ∧
  PV_B3P_Link_terminal_path_lanes_literal source.body9 ∧
  PV_B3P_Link_terminal_poseidon_selectors source.body10 ∧
  PV_B3P_Link_terminal_public_digest_lanes source.body11 ∧
  PV_B3P_Link_terminal_reconstruct_10 source.body12 ∧
  PV_B3P_Link_terminal_semantic_initial_and_absorption source.body13 ∧
  PV_B3P_Link_terminal_semantic_packed source.body14 ∧
  PV_B3P_Link_terminal_sum_high source.body15 ∧
  PV_B3P_Link_terminal_validate_transition source.body16 ∧
  PV_B3P_Link_copy_active_literal source.body17 ∧
  PV_B3P_Link_copy_pattern_values_literal source.body18 ∧
  PV_B3P_Link_copy_selector_mask_sum_16 source.body19 ∧
  PV_B3P_Link_field_qm31_m31_dot source.body20 ∧
  PV_B3P_Link_field_qm31_sum_products3_prepared source.body21 ∧
  PV_B3P_Link_poseidon_at_point source.body22 ∧
  PV_B3P_Link_poseidon_evaluate_state_only_poseidon_oracle_projected source.body23 ∧
  PV_B3P_Link_poseidon_expand source.body24 ∧
  PV_B3P_Link_poseidon_external_linear_lazy source.body25 ∧
  PV_B3P_Link_poseidon_external_linear_packed source.body26 ∧
  PV_B3P_Link_poseidon_external_local_packed_raw source.body27 ∧
  PV_B3P_Link_poseidon_full_round source.body28 ∧
  PV_B3P_Link_poseidon_full_round_m31_constants source.body29 ∧
  PV_B3P_Link_poseidon_full_round_m31_constants_packed source.body30 ∧
  PV_B3P_Link_poseidon_full_round_packed source.body31 ∧
  PV_B3P_Link_poseidon_internal_linear_lazy source.body32 ∧
  PV_B3P_Link_poseidon_interpolate_three_constant_columns source.body33 ∧
  PV_B3P_Link_poseidon_interpolated_internal_pair source.body34 ∧
  PV_B3P_Link_poseidon_leading_pair_packed source.body35

def explicit_model_bodies13 : ChangedBodies13 where
  body0 := (@reference_terminal.absorption_lanes_literal)
  body1 := (@reference_terminal.add_digest_binding)
  body2 := (@reference_terminal.add_path_lanes)
  body3 := (@reference_terminal.add_preweighted)
  body4 := (@reference_terminal.add_schedule_lanes)
  body5 := (@reference_terminal.add_value_lanes)
  body6 := (@reference_terminal.composition_parts)
  body7 := (@reference_terminal.equality_value)
  body8 := (@reference_terminal.occupancy_lanes_literal)
  body9 := (@reference_terminal.path_lanes_literal)
  body10 := (@reference_terminal.poseidon_selectors)
  body11 := (@reference_terminal.public_digest_lanes)
  body12 := (@reference_terminal.reconstruct_10)
  body13 := (@reference_terminal.semantic_initial_and_absorption)
  body14 := (@reference_terminal.semantic_packed)
  body15 := (fun (selectors : reference_copy_terminal.Selectors) ranges => sum_ranges_reference13 selectors.high ranges aspis_core.field.QM31.ZERO)
  body16 := (@reference_terminal.validate_transition)
  body17 := (@reference_copy_terminal.Selectors.active_literal)
  body18 := (@reference_copy_terminal.pattern_values_literal)
  body19 := (@reference_copy_terminal.selector_mask_sum_16)
  body20 := (@reference_field.qm31_m31_dot)
  body21 := (@reference_field.qm31_sum_products3_prepared)
  body22 := (@selector_reference13)
  body23 := (@reference_poseidon.evaluate_state_only_poseidon_oracle_projected)
  body24 := (@reference_copy_terminal.Selectors.expand)
  body25 := (@reference_poseidon.external_linear_lazy)
  body26 := (@reference_poseidon.external_linear_packed)
  body27 := (@reference_poseidon.external_local_packed_raw)
  body28 := (@reference_poseidon.full_round)
  body29 := (@reference_poseidon.full_round_m31_constants)
  body30 := (@reference_poseidon.full_round_m31_constants_packed)
  body31 := (@reference_poseidon.full_round_packed)
  body32 := (@reference_poseidon.internal_linear_lazy)
  body33 := (@reference_poseidon.interpolate_three_constant_columns)
  body34 := (@reference_poseidon.interpolated_internal_pair)
  body35 := (@reference_poseidon.leading_pair_packed)

/-- Joint satisfiability of the typed 36-function group, for a concrete MODEL
instance. It does not instantiate the actual deployed source interpretation. -/
theorem changed_bodies_satisfiable13 :
    PV_B3P_Link_changed_bodies explicit_model_bodies13 := by
  repeat' constructor
  all_goals
    repeat' intro
    rfl
#print axioms changed_bodies_satisfiable13
end
end PV_B3P_Groups13227
