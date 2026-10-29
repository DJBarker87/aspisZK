import PV_B3P_Success227
import PV_B3P_P227_01
import PV_B3P_RefFieldSuccess227
import PV_B3P_AccumulateSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_field_qm31_sum_products3_prepared (left : Array reference_field.PreparedQm31Multiplier 3#usize) (right : Array aspis_core.field.QM31 3#usize) :
    Success (reference_field.qm31_sum_products3_prepared left right) := by
  unfold reference_field.qm31_sum_products3_prepared
  dsimp only
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply index <;> scalar_tac
  intro pqm
  apply bind
  · apply total_reference_field_accumulate_prepared227
  intro sums1
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply index <;> scalar_tac
  intro pqm1
  apply bind
  · apply total_reference_field_accumulate_prepared227
  intro sums2
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply index <;> scalar_tac
  intro pqm2
  apply bind
  · apply total_reference_field_accumulate_prepared227
  intro sums3
  apply bind
  · apply index <;> scalar_tac
  intro a1
  apply bind
  · apply total_reference_field_reconstruct_component
  intro m0
  apply bind
  · apply index <;> scalar_tac
  intro a2
  apply bind
  · apply total_reference_field_reconstruct_component
  intro m1
  apply bind
  · apply index <;> scalar_tac
  intro a3
  apply bind
  · apply total_reference_field_reconstruct_component
  intro m2
  apply bind
  · apply total_reference_field_cm31_mul_r
  intro c
  apply bind
  · apply cadd
  intro c1
  apply bind
  · apply csub
  intro c2
  apply bind
  · apply csub
  intro c3
  exact ok _

#print axioms total_reference_field_qm31_sum_products3_prepared

theorem total_reference_field_qm31_m31_dot (weights : Array aspis_core.field.QM31 7#usize) (values : Array aspis_core.field.M31 7#usize) :
    Success (reference_field.qm31_m31_dot weights values) := by
  unfold reference_field.qm31_m31_dot
  dsimp only
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro m
  apply bind
  · exact ok _
  intro value
  apply bind
  · apply index <;> scalar_tac
  intro weight
  dsimp only
  apply bind
  · exact ok _
  intro i1
  apply bind
  · exact ok _
  intro i2
  apply bind
  · apply index <;> scalar_tac
  intro i3
  apply bind
  · exact ok _
  intro i4
  apply bind
  · apply update <;> scalar_tac
  intro raw2
  dsimp only
  apply bind
  · exact ok _
  intro i6
  apply bind
  · exact ok _
  intro i7
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply bind
  · exact ok _
  intro i9
  apply bind
  · apply update <;> scalar_tac
  intro raw3
  dsimp only
  apply bind
  · exact ok _
  intro i11
  apply bind
  · exact ok _
  intro i12
  apply bind
  · apply index <;> scalar_tac
  intro i13
  apply bind
  · exact ok _
  intro i14
  apply bind
  · apply update <;> scalar_tac
  intro raw4
  dsimp only
  apply bind
  · exact ok _
  intro i16
  apply bind
  · exact ok _
  intro i17
  apply bind
  · apply index <;> scalar_tac
  intro i18
  apply bind
  · exact ok _
  intro i19
  apply bind
  · apply update <;> scalar_tac
  intro raw5
  apply bind
  · apply index <;> scalar_tac
  intro m1
  apply bind
  · exact ok _
  intro value1
  apply bind
  · apply index <;> scalar_tac
  intro weight1
  dsimp only
  apply bind
  · exact ok _
  intro i21
  apply bind
  · exact ok _
  intro i22
  apply bind
  · apply index <;> scalar_tac
  intro i23
  apply bind
  · exact ok _
  intro i24
  apply bind
  · apply update <;> scalar_tac
  intro raw6
  dsimp only
  apply bind
  · exact ok _
  intro i26
  apply bind
  · exact ok _
  intro i27
  apply bind
  · apply index <;> scalar_tac
  intro i28
  apply bind
  · exact ok _
  intro i29
  apply bind
  · apply update <;> scalar_tac
  intro raw7
  dsimp only
  apply bind
  · exact ok _
  intro i31
  apply bind
  · exact ok _
  intro i32
  apply bind
  · apply index <;> scalar_tac
  intro i33
  apply bind
  · exact ok _
  intro i34
  apply bind
  · apply update <;> scalar_tac
  intro raw8
  dsimp only
  apply bind
  · exact ok _
  intro i36
  apply bind
  · exact ok _
  intro i37
  apply bind
  · apply index <;> scalar_tac
  intro i38
  apply bind
  · exact ok _
  intro i39
  apply bind
  · apply update <;> scalar_tac
  intro raw9
  apply bind
  · apply index <;> scalar_tac
  intro m2
  apply bind
  · exact ok _
  intro value2
  apply bind
  · apply index <;> scalar_tac
  intro weight2
  dsimp only
  apply bind
  · exact ok _
  intro i41
  apply bind
  · exact ok _
  intro i42
  apply bind
  · apply index <;> scalar_tac
  intro i43
  apply bind
  · exact ok _
  intro i44
  apply bind
  · apply update <;> scalar_tac
  intro raw10
  dsimp only
  apply bind
  · exact ok _
  intro i46
  apply bind
  · exact ok _
  intro i47
  apply bind
  · apply index <;> scalar_tac
  intro i48
  apply bind
  · exact ok _
  intro i49
  apply bind
  · apply update <;> scalar_tac
  intro raw11
  dsimp only
  apply bind
  · exact ok _
  intro i51
  apply bind
  · exact ok _
  intro i52
  apply bind
  · apply index <;> scalar_tac
  intro i53
  apply bind
  · exact ok _
  intro i54
  apply bind
  · apply update <;> scalar_tac
  intro raw12
  dsimp only
  apply bind
  · exact ok _
  intro i56
  apply bind
  · exact ok _
  intro i57
  apply bind
  · apply index <;> scalar_tac
  intro i58
  apply bind
  · exact ok _
  intro i59
  apply bind
  · apply update <;> scalar_tac
  intro raw13
  apply bind
  · apply index <;> scalar_tac
  intro m3
  apply bind
  · exact ok _
  intro value3
  apply bind
  · apply index <;> scalar_tac
  intro weight3
  dsimp only
  apply bind
  · exact ok _
  intro i61
  apply bind
  · exact ok _
  intro i62
  apply bind
  · apply index <;> scalar_tac
  intro i63
  apply bind
  · exact ok _
  intro i64
  apply bind
  · apply update <;> scalar_tac
  intro raw14
  dsimp only
  apply bind
  · exact ok _
  intro i66
  apply bind
  · exact ok _
  intro i67
  apply bind
  · apply index <;> scalar_tac
  intro i68
  apply bind
  · exact ok _
  intro i69
  apply bind
  · apply update <;> scalar_tac
  intro raw15
  dsimp only
  apply bind
  · exact ok _
  intro i71
  apply bind
  · exact ok _
  intro i72
  apply bind
  · apply index <;> scalar_tac
  intro i73
  apply bind
  · exact ok _
  intro i74
  apply bind
  · apply update <;> scalar_tac
  intro raw16
  dsimp only
  apply bind
  · exact ok _
  intro i76
  apply bind
  · exact ok _
  intro i77
  apply bind
  · apply index <;> scalar_tac
  intro i78
  apply bind
  · exact ok _
  intro i79
  apply bind
  · apply update <;> scalar_tac
  intro raw17
  apply bind
  · apply index <;> scalar_tac
  intro i80
  apply bind
  · apply reduce64
  intro m4
  apply bind
  · exact ok _
  intro i81
  apply bind
  · apply index <;> scalar_tac
  intro i82
  apply bind
  · exact ok _
  intro i83
  apply bind
  · apply update <;> scalar_tac
  intro sums1
  apply bind
  · apply index <;> scalar_tac
  intro i84
  apply bind
  · apply reduce64
  intro m5
  apply bind
  · exact ok _
  intro i85
  apply bind
  · apply index <;> scalar_tac
  intro i86
  apply bind
  · exact ok _
  intro i87
  apply bind
  · apply update <;> scalar_tac
  intro sums2
  apply bind
  · apply index <;> scalar_tac
  intro i88
  apply bind
  · apply reduce64
  intro m6
  apply bind
  · exact ok _
  intro i89
  apply bind
  · apply index <;> scalar_tac
  intro i90
  apply bind
  · exact ok _
  intro i91
  apply bind
  · apply update <;> scalar_tac
  intro sums3
  apply bind
  · apply index <;> scalar_tac
  intro i92
  apply bind
  · apply reduce64
  intro m7
  apply bind
  · exact ok _
  intro i93
  apply bind
  · apply index <;> scalar_tac
  intro i94
  apply bind
  · exact ok _
  intro i95
  apply bind
  · apply update <;> scalar_tac
  intro sums4
  dsimp only
  apply bind
  · apply index <;> scalar_tac
  intro m8
  apply bind
  · exact ok _
  intro value4
  apply bind
  · apply index <;> scalar_tac
  intro weight4
  dsimp only
  apply bind
  · exact ok _
  intro i97
  apply bind
  · exact ok _
  intro i98
  apply bind
  · apply index <;> scalar_tac
  intro i99
  apply bind
  · exact ok _
  intro i100
  apply bind
  · apply update <;> scalar_tac
  intro raw19
  dsimp only
  apply bind
  · exact ok _
  intro i102
  apply bind
  · exact ok _
  intro i103
  apply bind
  · apply index <;> scalar_tac
  intro i104
  apply bind
  · exact ok _
  intro i105
  apply bind
  · apply update <;> scalar_tac
  intro raw20
  dsimp only
  apply bind
  · exact ok _
  intro i107
  apply bind
  · exact ok _
  intro i108
  apply bind
  · apply index <;> scalar_tac
  intro i109
  apply bind
  · exact ok _
  intro i110
  apply bind
  · apply update <;> scalar_tac
  intro raw21
  dsimp only
  apply bind
  · exact ok _
  intro i112
  apply bind
  · exact ok _
  intro i113
  apply bind
  · apply index <;> scalar_tac
  intro i114
  apply bind
  · exact ok _
  intro i115
  apply bind
  · apply update <;> scalar_tac
  intro raw22
  apply bind
  · apply index <;> scalar_tac
  intro m9
  apply bind
  · exact ok _
  intro value5
  apply bind
  · apply index <;> scalar_tac
  intro weight5
  dsimp only
  apply bind
  · exact ok _
  intro i117
  apply bind
  · exact ok _
  intro i118
  apply bind
  · apply index <;> scalar_tac
  intro i119
  apply bind
  · exact ok _
  intro i120
  apply bind
  · apply update <;> scalar_tac
  intro raw23
  dsimp only
  apply bind
  · exact ok _
  intro i122
  apply bind
  · exact ok _
  intro i123
  apply bind
  · apply index <;> scalar_tac
  intro i124
  apply bind
  · exact ok _
  intro i125
  apply bind
  · apply update <;> scalar_tac
  intro raw24
  dsimp only
  apply bind
  · exact ok _
  intro i127
  apply bind
  · exact ok _
  intro i128
  apply bind
  · apply index <;> scalar_tac
  intro i129
  apply bind
  · exact ok _
  intro i130
  apply bind
  · apply update <;> scalar_tac
  intro raw25
  dsimp only
  apply bind
  · exact ok _
  intro i132
  apply bind
  · exact ok _
  intro i133
  apply bind
  · apply index <;> scalar_tac
  intro i134
  apply bind
  · exact ok _
  intro i135
  apply bind
  · apply update <;> scalar_tac
  intro raw26
  apply bind
  · apply index <;> scalar_tac
  intro m10
  apply bind
  · exact ok _
  intro value6
  apply bind
  · apply index <;> scalar_tac
  intro weight6
  dsimp only
  apply bind
  · exact ok _
  intro i137
  apply bind
  · exact ok _
  intro i138
  apply bind
  · apply index <;> scalar_tac
  intro i139
  apply bind
  · exact ok _
  intro i140
  apply bind
  · apply update <;> scalar_tac
  intro raw27
  dsimp only
  apply bind
  · exact ok _
  intro i142
  apply bind
  · exact ok _
  intro i143
  apply bind
  · apply index <;> scalar_tac
  intro i144
  apply bind
  · exact ok _
  intro i145
  apply bind
  · apply update <;> scalar_tac
  intro raw28
  dsimp only
  apply bind
  · exact ok _
  intro i147
  apply bind
  · exact ok _
  intro i148
  apply bind
  · apply index <;> scalar_tac
  intro i149
  apply bind
  · exact ok _
  intro i150
  apply bind
  · apply update <;> scalar_tac
  intro raw29
  dsimp only
  apply bind
  · exact ok _
  intro i152
  apply bind
  · exact ok _
  intro i153
  apply bind
  · apply index <;> scalar_tac
  intro i154
  apply bind
  · exact ok _
  intro i155
  apply bind
  · apply update <;> scalar_tac
  intro raw30
  apply bind
  · apply index <;> scalar_tac
  intro i156
  apply bind
  · apply reduce64
  intro m11
  apply bind
  · exact ok _
  intro i157
  apply bind
  · apply index <;> scalar_tac
  intro i158
  apply bind
  · exact ok _
  intro i159
  apply bind
  · apply update <;> scalar_tac
  intro sums5
  apply bind
  · apply index <;> scalar_tac
  intro i160
  apply bind
  · apply reduce64
  intro m12
  apply bind
  · exact ok _
  intro i161
  apply bind
  · apply index <;> scalar_tac
  intro i162
  apply bind
  · exact ok _
  intro i163
  apply bind
  · apply update <;> scalar_tac
  intro sums6
  apply bind
  · apply index <;> scalar_tac
  intro i164
  apply bind
  · apply reduce64
  intro m13
  apply bind
  · exact ok _
  intro i165
  apply bind
  · apply index <;> scalar_tac
  intro i166
  apply bind
  · exact ok _
  intro i167
  apply bind
  · apply update <;> scalar_tac
  intro sums7
  apply bind
  · apply index <;> scalar_tac
  intro i168
  apply bind
  · apply reduce64
  intro m14
  apply bind
  · exact ok _
  intro i169
  apply bind
  · apply index <;> scalar_tac
  intro i170
  apply bind
  · exact ok _
  intro i171
  apply bind
  · apply update <;> scalar_tac
  intro sums8
  apply bind
  · apply index <;> scalar_tac
  intro i172
  apply bind
  · apply reduce64
  intro m15
  apply bind
  · apply index <;> scalar_tac
  intro i173
  apply bind
  · apply reduce64
  intro m16
  apply bind
  · apply cnew
  intro c
  apply bind
  · apply index <;> scalar_tac
  intro i174
  apply bind
  · apply reduce64
  intro m17
  apply bind
  · apply index <;> scalar_tac
  intro i175
  apply bind
  · apply reduce64
  intro m18
  apply bind
  · apply cnew
  intro c1
  exact ok _

#print axioms total_reference_field_qm31_m31_dot

end PV_B3P_Success227
