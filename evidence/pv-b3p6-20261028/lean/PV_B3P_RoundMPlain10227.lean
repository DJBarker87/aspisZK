import PV_B3P_RoundMTail1004227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.M31.add reference_poseidon.pow5 Array.index_usize Array.update Array.index_mut_usize round_m_source10_04

theorem full_round_m31_constants_entry10 (state : RoundState10) (constants1 : Array U32 16#usize) :
    reference_poseidon.full_round_m31_constants state constants1 =
      (round_m_group10_00 constants1 state >>= round_m_source10_04 reference_poseidon.external_linear_lazy constants1) := by
  conv_rhs => simp only [round_m_group10_00,PV_B3P_Ordered227.fold,round_m_step10,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  apply bind_equal9
  intro head_0
  apply bind_equal9
  intro head_1
  apply bind_equal9
  intro head_2
  apply bind_equal9
  intro head_3
  rcases head_3 with ⟨part_3,back_3⟩
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
  rcases head_10 with ⟨part_10,back_10⟩
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
  rcases head_17 with ⟨part_17,back_17⟩
  apply bind_equal9
  intro head_18
  apply bind_equal9
  intro head_19
  apply bind_equal9
  intro head_20
  apply bind_equal9
  intro head_21
  apply bind_equal9
  intro head_22
  apply bind_equal9
  intro head_23
  apply bind_equal9
  intro head_24
  rcases head_24 with ⟨part_24,back_24⟩
  apply bind_equal9
  intro head_25
  apply bind_equal9
  intro head_26
  apply bind_equal9
  intro head_27
  unfold round_m_source10_04
  rfl

theorem full_round_m31_constants_body_binding10 (state : RoundState10) (constants1 : Array U32 16#usize) :
    reference_poseidon.full_round_m31_constants state constants1 =
      (round_m_group10_00 constants1 state >>= round_m_folded10_04 reference_poseidon.external_linear_lazy constants1) := by
  rw [full_round_m31_constants_entry10]
  apply congrArg (fun next => round_m_group10_00 constants1 state >>= next)
  funext next
  exact round_m_factor10_04 reference_poseidon.external_linear_lazy constants1 next
#print axioms full_round_m31_constants_entry10
#print axioms full_round_m31_constants_body_binding10
end PV_B3P_Binding10227
