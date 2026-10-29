import PV_B3P_LinkGroup13227
import PV_B3P_MaskCorrection14227
import PV_B3P_SelectorCorrection14227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227 PV_B3P_Groups13227
set_option autoImplicit false
noncomputable section
/-- Corrected 36-body group. All prior total predicates are retained except the
refuted native instances, now explicitly guarded with their caller obligations. -/
structure CorrectedLinks14 (source : ChangedBodies13) (called : U16 → Prop)
    (constructor : Usize → SelectorFn) (blocks : Usize) : Prop where
  link0 : PV_B3P_Link_terminal_absorption_lanes_literal source.body0
  link1 : PV_B3P_Link_terminal_add_digest_binding source.body1
  link2 : PV_B3P_Link_terminal_add_path_lanes source.body2
  link3 : PV_B3P_Link_terminal_add_preweighted source.body3
  link4 : PV_B3P_Link_terminal_add_schedule_lanes source.body4
  link5 : PV_B3P_Link_terminal_add_value_lanes source.body5
  link6 : PV_B3P_Link_terminal_composition_parts source.body6
  link7 : PV_B3P_Link_terminal_equality_value source.body7
  link8 : PV_B3P_Link_terminal_occupancy_lanes_literal source.body8
  link9 : PV_B3P_Link_terminal_path_lanes_literal source.body9
  link10 : PV_B3P_Link_terminal_poseidon_selectors source.body10
  link11 : PV_B3P_Link_terminal_public_digest_lanes source.body11
  link12 : PV_B3P_Link_terminal_reconstruct_10 source.body12
  link13 : PV_B3P_Link_terminal_semantic_initial_and_absorption source.body13
  link14 : PV_B3P_Link_terminal_semantic_packed source.body14
  link15 : PV_B3P_Link_terminal_sum_high source.body15
  link16 : PV_B3P_Link_terminal_validate_transition source.body16
  link17 : PV_B3P_Link_copy_active_literal source.body17
  link18 : PV_B3P_Link_copy_pattern_values_literal source.body18
  link19 : PV_B3P_Link_mask_on_domain source.body19
  link20 : PV_B3P_Link_field_qm31_m31_dot source.body20
  link21 : PV_B3P_Link_field_qm31_sum_products3_prepared source.body21
  link22 : PV_B3P_Link_constructor_on_layout constructor
  link23 : PV_B3P_Link_poseidon_evaluate_state_only_poseidon_oracle_projected source.body23
  link24 : PV_B3P_Link_poseidon_expand source.body24
  link25 : PV_B3P_Link_poseidon_external_linear_lazy source.body25
  link26 : PV_B3P_Link_poseidon_external_linear_packed source.body26
  link27 : PV_B3P_Link_poseidon_external_local_packed_raw source.body27
  link28 : PV_B3P_Link_poseidon_full_round source.body28
  link29 : PV_B3P_Link_poseidon_full_round_m31_constants source.body29
  link30 : PV_B3P_Link_poseidon_full_round_m31_constants_packed source.body30
  link31 : PV_B3P_Link_poseidon_full_round_packed source.body31
  link32 : PV_B3P_Link_poseidon_internal_linear_lazy source.body32
  link33 : PV_B3P_Link_poseidon_interpolate_three_constant_columns source.body33
  link34 : PV_B3P_Link_poseidon_interpolated_internal_pair source.body34
  link35 : PV_B3P_Link_poseidon_leading_pair_packed source.body35
  mask_domain : PV_B3P_Link_mask_call_domain called
  constructor_layout : PV_B3P_Link_constructor_call_layout blocks
  constructor_native : PV_B3P_Link_constructor_native source.body22 constructor blocks

def corrected_model_bodies14 : ChangedBodies13 :=
  { explicit_model_bodies13 with body19 := PV_B3P_Binding11227.source_mask11 }

theorem corrected_links_witness14 :
    CorrectedLinks14 corrected_model_bodies14 frozen_calls14 constructor14 57#usize where
  link0 := rfl
  link1 := rfl
  link2 := rfl
  link3 := rfl
  link4 := rfl
  link5 := rfl
  link6 := rfl
  link7 := rfl
  link8 := rfl
  link9 := rfl
  link10 := rfl
  link11 := rfl
  link12 := rfl
  link13 := rfl
  link14 := rfl
  link15 := (fun _ _ => rfl)
  link16 := rfl
  link17 := rfl
  link18 := rfl
  link19 := mask_direct14
  link20 := rfl
  link21 := rfl
  link22 := constructor_on_layout14
  link23 := rfl
  link24 := rfl
  link25 := rfl
  link26 := rfl
  link27 := rfl
  link28 := rfl
  link29 := rfl
  link30 := rfl
  link31 := rfl
  link32 := rfl
  link33 := rfl
  link34 := rfl
  link35 := rfl
  mask_domain := mask_call_domain14
  constructor_layout := rfl
  constructor_native := constructor_target14.symm

#print axioms corrected_links_witness14
end
end PV_B3P_Correct14227
