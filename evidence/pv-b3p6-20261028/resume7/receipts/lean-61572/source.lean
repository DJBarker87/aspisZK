import PV_B3P_RoundSuccess227
import PV_B3P_DotSuccess227
import PV_B3P_RefPackSuccess227
import PV_B3P_P227_06
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_poseidon_internal_round (state : Array aspis_core.field.QM31 16#usize) (constant1 : aspis_core.field.QM31) :
    Success (reference_poseidon.internal_round state constant1) := by
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply qadd
  intro q1
  apply bind
  · apply total_reference_poseidon_pow5
  intro q2
  apply bind
  · apply update <;> scalar_tac
  intro state1
  apply total_reference_poseidon_internal_linear_lazy

#print axioms total_reference_poseidon_internal_round

theorem total_reference_poseidon_leading_pair_packed (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    Success (reference_poseidon.leading_pair_packed openings) := by
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply qadd
  intro q2
  apply bind
  · apply update <;> scalar_tac
  intro state
  apply bind
  · apply index <;> scalar_tac
  intro q3
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply qadd
  intro q5
  apply bind
  · apply update <;> scalar_tac
  intro state1
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply bind
  · apply index <;> scalar_tac
  intro q7
  apply bind
  · apply qadd
  intro q8
  apply bind
  · apply update <;> scalar_tac
  intro state2
  apply bind
  · apply index <;> scalar_tac
  intro q9
  apply bind
  · apply index <;> scalar_tac
  intro q10
  apply bind
  · apply qadd
  intro q11
  apply bind
  · apply update <;> scalar_tac
  intro state3
  apply bind
  · apply index <;> scalar_tac
  intro q12
  apply bind
  · apply index <;> scalar_tac
  intro q13
  apply bind
  · apply qadd
  intro q14
  apply bind
  · apply update <;> scalar_tac
  intro state4
  apply bind
  · apply index <;> scalar_tac
  intro q15
  apply bind
  · apply index <;> scalar_tac
  intro q16
  apply bind
  · apply qadd
  intro q17
  apply bind
  · apply update <;> scalar_tac
  intro state5
  apply bind
  · apply index <;> scalar_tac
  intro q18
  apply bind
  · apply index <;> scalar_tac
  intro q19
  apply bind
  · apply qadd
  intro q20
  apply bind
  · apply update <;> scalar_tac
  intro state6
  apply bind
  · apply index <;> scalar_tac
  intro q21
  apply bind
  · apply index <;> scalar_tac
  intro q22
  apply bind
  · apply qadd
  intro q23
  apply bind
  · apply update <;> scalar_tac
  intro state7
  apply bind
  · apply total_reference_poseidon_external_linear_lazy
  intro state8
  apply bind
  · apply index <;> scalar_tac
  intro a
  apply bind
  · apply total_reference_poseidon_full_round_m31_constants
  intro a1
  apply bind
  · apply index <;> scalar_tac
  intro a2
  apply total_reference_poseidon_full_round_m31_constants_packed

#print axioms total_reference_poseidon_leading_pair_packed

theorem total_reference_poseidon_interpolate_three_constant_limb (weight0 : Std.U32) (weight1 : Std.U32) (weight2 : Std.U32) (constant0 : Std.U32) (constant1 : Std.U32) (constant2 : Std.U32) :
    Success (reference_poseidon.interpolate_three_constant_limb weight0 weight1 weight2 constant0 constant1 constant2) := by
  apply lift_total
  apply lift_total
  apply lift_total
  apply lift_total
  apply lift_total
  apply lift_total
  apply lift_total
  apply lift_total
  apply lift_total
  apply lift_total
  apply lift_total
  apply reduce64

#print axioms total_reference_poseidon_interpolate_three_constant_limb

theorem total_reference_poseidon_interpolate_column227 (weights : Array aspis_core.field.QM31 3#usize) (column0 : Std.U32) (column1 : Std.U32) (column2 : Std.U32) :
    Success (reference_poseidon.interpolate_column227 weights column0 column1 column2) := by
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply total_reference_poseidon_interpolate_three_constant_limb
  intro m
  apply bind
  · apply total_reference_poseidon_interpolate_three_constant_limb
  intro m1
  apply bind
  · apply cnew
  intro c
  apply bind
  · apply total_reference_poseidon_interpolate_three_constant_limb
  intro m2
  apply bind
  · apply total_reference_poseidon_interpolate_three_constant_limb
  intro m3
  apply bind
  · apply cnew
  intro c1
  exact ok _

#print axioms total_reference_poseidon_interpolate_column227

theorem total_reference_poseidon_interpolate_three_constant_columns (weights : Array aspis_core.field.QM31 3#usize) (column0 : Array Std.U32 16#usize) (column1 : Array Std.U32 16#usize) (column2 : Array Std.U32 16#usize) :
    Success (reference_poseidon.interpolate_three_constant_columns weights column0 column1 column2) := by
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply bind
  · apply index <;> scalar_tac
  intro i1
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q
  apply bind
  · apply update <;> scalar_tac
  intro output1
  apply bind
  · apply index <;> scalar_tac
  intro i3
  apply bind
  · apply index <;> scalar_tac
  intro i4
  apply bind
  · apply index <;> scalar_tac
  intro i5
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q1
  apply bind
  · apply update <;> scalar_tac
  intro output2
  apply bind
  · apply index <;> scalar_tac
  intro i6
  apply bind
  · apply index <;> scalar_tac
  intro i7
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q2
  apply bind
  · apply update <;> scalar_tac
  intro output3
  apply bind
  · apply index <;> scalar_tac
  intro i9
  apply bind
  · apply index <;> scalar_tac
  intro i10
  apply bind
  · apply index <;> scalar_tac
  intro i11
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q3
  apply bind
  · apply update <;> scalar_tac
  intro output4
  apply bind
  · apply index <;> scalar_tac
  intro i12
  apply bind
  · apply index <;> scalar_tac
  intro i13
  apply bind
  · apply index <;> scalar_tac
  intro i14
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q4
  apply bind
  · apply update <;> scalar_tac
  intro output5
  apply bind
  · apply index <;> scalar_tac
  intro i15
  apply bind
  · apply index <;> scalar_tac
  intro i16
  apply bind
  · apply index <;> scalar_tac
  intro i17
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q5
  apply bind
  · apply update <;> scalar_tac
  intro output6
  apply bind
  · apply index <;> scalar_tac
  intro i18
  apply bind
  · apply index <;> scalar_tac
  intro i19
  apply bind
  · apply index <;> scalar_tac
  intro i20
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q6
  apply bind
  · apply update <;> scalar_tac
  intro output7
  apply bind
  · apply index <;> scalar_tac
  intro i21
  apply bind
  · apply index <;> scalar_tac
  intro i22
  apply bind
  · apply index <;> scalar_tac
  intro i23
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q7
  apply bind
  · apply update <;> scalar_tac
  intro output8
  apply bind
  · apply index <;> scalar_tac
  intro i24
  apply bind
  · apply index <;> scalar_tac
  intro i25
  apply bind
  · apply index <;> scalar_tac
  intro i26
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q8
  apply bind
  · apply update <;> scalar_tac
  intro output9
  apply bind
  · apply index <;> scalar_tac
  intro i27
  apply bind
  · apply index <;> scalar_tac
  intro i28
  apply bind
  · apply index <;> scalar_tac
  intro i29
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q9
  apply bind
  · apply update <;> scalar_tac
  intro output10
  apply bind
  · apply index <;> scalar_tac
  intro i30
  apply bind
  · apply index <;> scalar_tac
  intro i31
  apply bind
  · apply index <;> scalar_tac
  intro i32
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q10
  apply bind
  · apply update <;> scalar_tac
  intro output11
  apply bind
  · apply index <;> scalar_tac
  intro i33
  apply bind
  · apply index <;> scalar_tac
  intro i34
  apply bind
  · apply index <;> scalar_tac
  intro i35
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q11
  apply bind
  · apply update <;> scalar_tac
  intro output12
  apply bind
  · apply index <;> scalar_tac
  intro i36
  apply bind
  · apply index <;> scalar_tac
  intro i37
  apply bind
  · apply index <;> scalar_tac
  intro i38
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q12
  apply bind
  · apply update <;> scalar_tac
  intro output13
  apply bind
  · apply index <;> scalar_tac
  intro i39
  apply bind
  · apply index <;> scalar_tac
  intro i40
  apply bind
  · apply index <;> scalar_tac
  intro i41
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q13
  apply bind
  · apply update <;> scalar_tac
  intro output14
  apply bind
  · apply index <;> scalar_tac
  intro i42
  apply bind
  · apply index <;> scalar_tac
  intro i43
  apply bind
  · apply index <;> scalar_tac
  intro i44
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q14
  apply bind
  · apply update <;> scalar_tac
  intro output15
  apply bind
  · apply index <;> scalar_tac
  intro i45
  apply bind
  · apply index <;> scalar_tac
  intro i46
  apply bind
  · apply index <;> scalar_tac
  intro i47
  apply bind
  · apply total_reference_poseidon_interpolate_column227
  intro q15
  apply update <;> scalar_tac

#print axioms total_reference_poseidon_interpolate_three_constant_columns

theorem total_reference_poseidon_interpolated_full_pair_packed (state : Array aspis_core.field.QM31 16#usize) (local1 : Array aspis_core.field.QM31 16#usize) :
    Success (reference_poseidon.interpolated_full_pair_packed state local1) := by
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply index <;> scalar_tac
  intro a
  apply bind
  · apply index <;> scalar_tac
  intro a1
  apply bind
  · apply index <;> scalar_tac
  intro a2
  apply bind
  · apply total_reference_poseidon_interpolate_three_constant_columns
  intro even
  apply bind
  · apply index <;> scalar_tac
  intro a3
  apply bind
  · apply index <;> scalar_tac
  intro a4
  apply bind
  · apply index <;> scalar_tac
  intro a5
  apply bind
  · apply total_reference_poseidon_interpolate_three_constant_columns
  intro odd
  apply bind
  · apply total_reference_poseidon_full_round
  intro a6
  apply total_reference_poseidon_full_round_packed

#print axioms total_reference_poseidon_interpolated_full_pair_packed

theorem total_reference_poseidon_interpolated_internal_pair (state : Array aspis_core.field.QM31 16#usize) (local1 : Array aspis_core.field.QM31 16#usize) :
    Success (reference_poseidon.interpolated_internal_pair state local1) := by
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply index <;> scalar_tac
  intro q3
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply index <;> scalar_tac
  intro q5
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i5
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i11
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i14
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i17
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i20
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i24
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i28
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i32
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i36
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i40
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i44
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i48
  apply bind
  · apply total_reference_field_qm31_m31_dot
  intro even
  apply bind
  · apply total_reference_field_qm31_m31_dot
  intro odd
  apply bind
  · apply total_reference_poseidon_internal_round
  intro a
  apply total_reference_poseidon_internal_round

#print axioms total_reference_poseidon_interpolated_internal_pair

theorem total_reference_poseidon_evaluate_state_only_poseidon_oracle_projected (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) :
    Success (reference_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors) := by
  apply bind
  · apply index <;> scalar_tac
  intro leading_low
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply qadd
  intro q1
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply qadd
  intro q3
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply qadd
  intro full_low
  apply bind
  · apply index <;> scalar_tac
  intro q5
  apply bind
  · apply qadd
  intro q6
  apply bind
  · apply index <;> scalar_tac
  intro q7
  apply bind
  · apply qadd
  intro q8
  apply bind
  · apply index <;> scalar_tac
  intro q9
  apply bind
  · apply qadd
  intro q10
  apply bind
  · apply index <;> scalar_tac
  intro q11
  apply bind
  · apply qadd
  intro q12
  apply bind
  · apply index <;> scalar_tac
  intro q13
  apply bind
  · apply qadd
  intro q14
  apply bind
  · apply index <;> scalar_tac
  intro q15
  apply bind
  · apply qadd
  intro q16
  apply bind
  · apply index <;> scalar_tac
  intro q17
  apply bind
  · apply qadd
  intro internal_low
  apply bind
  · apply total_reference_poseidon_leading_pair_packed
  intro leading
  apply bind
  · apply total_reference_poseidon_interpolated_full_pair_packed
  intro full
  apply bind
  · apply total_reference_poseidon_interpolated_internal_pair
  intro internal
  apply bind
  · apply total_reference_field_PreparedQm31Multiplier_new
  intro pqm
  apply bind
  · apply total_reference_field_PreparedQm31Multiplier_new
  intro pqm1
  apply bind
  · apply total_reference_field_PreparedQm31Multiplier_new
  intro pqm2
  apply bind
  · apply total_reference_field_PreparedQm31Multiplier_new
  intro prepared_block
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q18
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q19
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q20
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q21
  apply lift_total
  apply bind
  · apply total_reference_field_qm31_pack_base4 <;> scalar_tac
  intro target
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q22
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q23
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q24
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q25
  apply lift_total
  apply bind
  · apply total_reference_field_qm31_pack_base4 <;> scalar_tac
  intro internal1
  apply bind
  · apply index <;> scalar_tac
  intro q26
  apply bind
  · apply qsub
  intro q27
  apply bind
  · apply index <;> scalar_tac
  intro q28
  apply bind
  · apply qsub
  intro q29
  apply bind
  · apply qsub
  intro q30
  apply bind
  · apply total_reference_field_qm31_sum_products3_prepared
  intro q31
  apply bind
  · apply total_reference_field_PreparedQm31Multiplier_mul
  intro q32
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q33
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q34
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q35
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q36
  apply lift_total
  apply bind
  · apply total_reference_field_qm31_pack_base4 <;> scalar_tac
  intro target1
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q37
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q38
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q39
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q40
  apply lift_total
  apply bind
  · apply total_reference_field_qm31_pack_base4 <;> scalar_tac
  intro internal2
  apply bind
  · apply index <;> scalar_tac
  intro q41
  apply bind
  · apply qsub
  intro q42
  apply bind
  · apply index <;> scalar_tac
  intro q43
  apply bind
  · apply qsub
  intro q44
  apply bind
  · apply qsub
  intro q45
  apply bind
  · apply total_reference_field_qm31_sum_products3_prepared
  intro q46
  apply bind
  · apply total_reference_field_PreparedQm31Multiplier_mul
  intro q47
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q48
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q49
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q50
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q51
  apply lift_total
  apply bind
  · apply total_reference_field_qm31_pack_base4 <;> scalar_tac
  intro target2
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q52
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q53
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q54
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q55
  apply lift_total
  apply bind
  · apply total_reference_field_qm31_pack_base4 <;> scalar_tac
  intro internal3
  apply bind
  · apply index <;> scalar_tac
  intro q56
  apply bind
  · apply qsub
  intro q57
  apply bind
  · apply index <;> scalar_tac
  intro q58
  apply bind
  · apply qsub
  intro q59
  apply bind
  · apply qsub
  intro q60
  apply bind
  · apply total_reference_field_qm31_sum_products3_prepared
  intro q61
  apply bind
  · apply total_reference_field_PreparedQm31Multiplier_mul
  intro q62
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q63
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q64
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q65
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q66
  apply lift_total
  apply bind
  · apply total_reference_field_qm31_pack_base4 <;> scalar_tac
  intro target3
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q67
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q68
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q69
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q70
  apply lift_total
  apply bind
  · apply total_reference_field_qm31_pack_base4 <;> scalar_tac
  intro internal4
  apply bind
  · apply index <;> scalar_tac
  intro q71
  apply bind
  · apply qsub
  intro q72
  apply bind
  · apply index <;> scalar_tac
  intro q73
  apply bind
  · apply qsub
  intro q74
  apply bind
  · apply qsub
  intro q75
  apply bind
  · apply total_reference_field_qm31_sum_products3_prepared
  intro q76
  apply bind
  · apply total_reference_field_PreparedQm31Multiplier_mul
  intro q77
  exact ok _

#print axioms total_reference_poseidon_evaluate_state_only_poseidon_oracle_projected

end PV_B3P_Success227
