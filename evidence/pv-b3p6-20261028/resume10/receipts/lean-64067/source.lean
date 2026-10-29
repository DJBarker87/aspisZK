import PV_B3P_RoundQTail1004227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.M31.add reference_poseidon.pow5 Array.index_usize Array.update Array.index_mut_usize round_q_source10_04

theorem full_round_entry10 (state : RoundState10) (constants1 : Array aspis_core.field.QM31 16#usize) :
    reference_poseidon.full_round state constants1 =
      (round_q_group10_00 constants1 state >>= round_q_source10_04 reference_poseidon.external_linear_lazy constants1) := by
  conv_rhs => simp only [round_q_group10_00,PV_B3P_Ordered227.fold,round_q_step10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  apply bind_equal9
  intro head_0
  apply bind_equal9
  intro head_1
  apply bind_equal9
  intro head_2
  apply bind_equal9
  intro head_3
  apply bind_equal9
  intro head_4
  apply bind_equal9
  intro head_5
  apply bind_equal9
  intro head_6
  apply bind_equal9
  intro head_7
  apply bind_equal9
  intro head_8
  apply bind_equal9
  intro head_9
  apply bind_equal9
  intro head_10
  apply bind_equal9
  intro head_11
  apply bind_equal9
  intro head_12
  apply bind_equal9
  intro head_13
  apply bind_equal9
  intro head_14
  apply bind_equal9
  intro head_15
  apply bind_equal9
  intro head_16
  apply bind_equal9
  intro head_17
  apply bind_equal9
  intro head_18
  apply bind_equal9
  intro head_19
  unfold round_q_source10_04
  rfl

theorem full_round_body_binding10 (state : RoundState10) (constants1 : Array aspis_core.field.QM31 16#usize) :
    reference_poseidon.full_round state constants1 =
      (round_q_group10_00 constants1 state >>= round_q_folded10_04 reference_poseidon.external_linear_lazy constants1) := by
  rw [full_round_entry10]
  apply congrArg (fun next => round_q_group10_00 constants1 state >>= next)
  funext next
  exact round_q_factor10_04 reference_poseidon.external_linear_lazy constants1 next
#print axioms full_round_entry10
#print axioms full_round_body_binding10
end PV_B3P_Binding10227
