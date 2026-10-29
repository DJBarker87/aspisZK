import PV_B3P_TopDown13227
namespace PV_B3P_Links13227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
noncomputable section
/-- Every source_model argument is UNINSTANTIATED until exact source association.
These predicates are not axioms, native implementations, or closure claims. -/
def PV_B3P_Link_terminal_absorption_lanes_literal (source_model : _) : Prop := source_model = @reference_terminal.absorption_lanes_literal
#print PV_B3P_Link_terminal_absorption_lanes_literal

def PV_B3P_Link_terminal_add_digest_binding (source_model : _) : Prop := source_model = @reference_terminal.add_digest_binding
#print PV_B3P_Link_terminal_add_digest_binding

def PV_B3P_Link_terminal_add_path_lanes (source_model : _) : Prop := source_model = @reference_terminal.add_path_lanes
#print PV_B3P_Link_terminal_add_path_lanes

def PV_B3P_Link_terminal_add_preweighted (source_model : _) : Prop := source_model = @reference_terminal.add_preweighted
#print PV_B3P_Link_terminal_add_preweighted

def PV_B3P_Link_terminal_add_schedule_lanes (source_model : _) : Prop := source_model = @reference_terminal.add_schedule_lanes
#print PV_B3P_Link_terminal_add_schedule_lanes

def PV_B3P_Link_terminal_add_value_lanes (source_model : _) : Prop := source_model = @reference_terminal.add_value_lanes
#print PV_B3P_Link_terminal_add_value_lanes

def PV_B3P_Link_terminal_composition_parts (source_model : _) : Prop := source_model = @reference_terminal.composition_parts
#print PV_B3P_Link_terminal_composition_parts

def PV_B3P_Link_terminal_equality_value (source_model : _) : Prop := source_model = @reference_terminal.equality_value
#print PV_B3P_Link_terminal_equality_value

def PV_B3P_Link_terminal_occupancy_lanes_literal (source_model : _) : Prop := source_model = @reference_terminal.occupancy_lanes_literal
#print PV_B3P_Link_terminal_occupancy_lanes_literal

def PV_B3P_Link_terminal_path_lanes_literal (source_model : _) : Prop := source_model = @reference_terminal.path_lanes_literal
#print PV_B3P_Link_terminal_path_lanes_literal

def PV_B3P_Link_terminal_poseidon_selectors (source_model : _) : Prop := source_model = @reference_terminal.poseidon_selectors
#print PV_B3P_Link_terminal_poseidon_selectors

def PV_B3P_Link_terminal_public_digest_lanes (source_model : _) : Prop := source_model = @reference_terminal.public_digest_lanes
#print PV_B3P_Link_terminal_public_digest_lanes

def PV_B3P_Link_terminal_reconstruct_10 (source_model : _) : Prop := source_model = @reference_terminal.reconstruct_10
#print PV_B3P_Link_terminal_reconstruct_10

def PV_B3P_Link_terminal_semantic_initial_and_absorption (source_model : _) : Prop := source_model = @reference_terminal.semantic_initial_and_absorption
#print PV_B3P_Link_terminal_semantic_initial_and_absorption

def PV_B3P_Link_terminal_semantic_packed (source_model : _) : Prop := source_model = @reference_terminal.semantic_packed
#print PV_B3P_Link_terminal_semantic_packed

def PV_B3P_Link_terminal_validate_transition (source_model : _) : Prop := source_model = @reference_terminal.validate_transition
#print PV_B3P_Link_terminal_validate_transition

def PV_B3P_Link_copy_active_literal (source_model : _) : Prop := source_model = @reference_copy_terminal.Selectors.active_literal
#print PV_B3P_Link_copy_active_literal

def PV_B3P_Link_copy_pattern_values_literal (source_model : _) : Prop := source_model = @reference_copy_terminal.pattern_values_literal
#print PV_B3P_Link_copy_pattern_values_literal

def PV_B3P_Link_copy_selector_mask_sum_16 (source_model : _) : Prop := source_model = @reference_copy_terminal.selector_mask_sum_16
#print PV_B3P_Link_copy_selector_mask_sum_16

def PV_B3P_Link_field_qm31_m31_dot (source_model : _) : Prop := source_model = @reference_field.qm31_m31_dot
#print PV_B3P_Link_field_qm31_m31_dot

def PV_B3P_Link_field_qm31_sum_products3_prepared (source_model : _) : Prop := source_model = @reference_field.qm31_sum_products3_prepared
#print PV_B3P_Link_field_qm31_sum_products3_prepared

def PV_B3P_Link_poseidon_evaluate_state_only_poseidon_oracle_projected (source_model : _) : Prop := source_model = @reference_poseidon.evaluate_state_only_poseidon_oracle_projected
#print PV_B3P_Link_poseidon_evaluate_state_only_poseidon_oracle_projected

def PV_B3P_Link_poseidon_external_linear_lazy (source_model : _) : Prop := source_model = @reference_poseidon.external_linear_lazy
#print PV_B3P_Link_poseidon_external_linear_lazy

def PV_B3P_Link_poseidon_external_linear_packed (source_model : _) : Prop := source_model = @reference_poseidon.external_linear_packed
#print PV_B3P_Link_poseidon_external_linear_packed

def PV_B3P_Link_poseidon_external_local_packed_raw (source_model : _) : Prop := source_model = @reference_poseidon.external_local_packed_raw
#print PV_B3P_Link_poseidon_external_local_packed_raw

def PV_B3P_Link_poseidon_full_round (source_model : _) : Prop := source_model = @reference_poseidon.full_round
#print PV_B3P_Link_poseidon_full_round

def PV_B3P_Link_poseidon_full_round_m31_constants (source_model : _) : Prop := source_model = @reference_poseidon.full_round_m31_constants
#print PV_B3P_Link_poseidon_full_round_m31_constants

def PV_B3P_Link_poseidon_full_round_m31_constants_packed (source_model : _) : Prop := source_model = @reference_poseidon.full_round_m31_constants_packed
#print PV_B3P_Link_poseidon_full_round_m31_constants_packed

def PV_B3P_Link_poseidon_full_round_packed (source_model : _) : Prop := source_model = @reference_poseidon.full_round_packed
#print PV_B3P_Link_poseidon_full_round_packed

def PV_B3P_Link_poseidon_internal_linear_lazy (source_model : _) : Prop := source_model = @reference_poseidon.internal_linear_lazy
#print PV_B3P_Link_poseidon_internal_linear_lazy

def PV_B3P_Link_poseidon_interpolate_three_constant_columns (source_model : _) : Prop := source_model = @reference_poseidon.interpolate_three_constant_columns
#print PV_B3P_Link_poseidon_interpolate_three_constant_columns

def PV_B3P_Link_poseidon_interpolated_internal_pair (source_model : _) : Prop := source_model = @reference_poseidon.interpolated_internal_pair
#print PV_B3P_Link_poseidon_interpolated_internal_pair

def PV_B3P_Link_poseidon_leading_pair_packed (source_model : _) : Prop := source_model = @reference_poseidon.leading_pair_packed
#print PV_B3P_Link_poseidon_leading_pair_packed

/-- Ordered list adapter for the exact source range-slice traversal. -/
def sum_ranges_reference13 (high : Array aspis_core.field.QM31 64#usize) :
    List (Usize × Usize) → aspis_core.field.QM31 → Result aspis_core.field.QM31
  | [], sum => .ok sum
  | (start, finish)::ranges, sum => do
      let next ← reference_terminal.sum_interval227 high sum start finish
      sum_ranges_reference13 high ranges next
def PV_B3P_Link_terminal_sum_high
    (source_model : reference_copy_terminal.Selectors → List (Usize × Usize) → Result aspis_core.field.QM31) : Prop :=
  ∀ selectors ranges, source_model selectors ranges =
    sum_ranges_reference13 selectors.high ranges aspis_core.field.QM31.ZERO
#print PV_B3P_Link_terminal_sum_high

/-- Source-only Poseidon expand, after an explicit checked slice adapter. -/
def PV_B3P_Link_poseidon_expand
    (source_model : (N : Usize) → Array aspis_core.field.QM31 10#usize → Usize → Usize → Result (Array aspis_core.field.QM31 N)) : Prop :=
  source_model = reference_copy_terminal.Selectors.expand

/-- Source-only selector constructor; the adapter must retain all bounds/error paths. -/
def selector_reference13 (point : Array aspis_core.field.QM31 10#usize) :
    Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors := do
  let selectors ← reference_copy_terminal.Selectors.at_point point
  reference_terminal.poseidon_selectors selectors

def PV_B3P_Link_poseidon_at_point
    (source_model : Array aspis_core.field.QM31 10#usize → Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) : Prop :=
  source_model = selector_reference13
#print PV_B3P_Link_poseidon_expand
#print PV_B3P_Link_poseidon_at_point
end
end PV_B3P_Links13227
