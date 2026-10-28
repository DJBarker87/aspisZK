import PV_B3P_Success227
import PV_B3P_P227_02
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_poseidon_pow5 (value : aspis_core.field.QM31) :
    Success (reference_poseidon.pow5 value) := by
  unfold reference_poseidon.pow5
  apply bind
  · apply qsquare
  intro square
  apply bind
  · apply qsquare
  intro q
  apply qmul

#print axioms total_reference_poseidon_pow5

theorem total_reference_poseidon_extension_limbs (value : aspis_core.field.QM31) :
    Success (reference_poseidon.extension_limbs value) := by
  unfold reference_poseidon.extension_limbs
  exact ok _

#print axioms total_reference_poseidon_extension_limbs

theorem total_reference_poseidon_extension_from_raw_limbs (limbs : Array Std.U64 4#usize) :
    Success (reference_poseidon.extension_from_raw_limbs limbs) := by
  unfold reference_poseidon.extension_from_raw_limbs
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply bind
  · apply reduce62
  intro m
  apply bind
  · apply index <;> scalar_tac
  intro i1
  apply bind
  · apply reduce62
  intro m1
  apply bind
  · apply cnew
  intro c
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply bind
  · apply reduce62
  intro m2
  apply bind
  · apply index <;> scalar_tac
  intro i3
  apply bind
  · apply reduce62
  intro m3
  apply bind
  · apply cnew
  intro c1
  exact ok _

#print axioms total_reference_poseidon_extension_from_raw_limbs

theorem total_reference_poseidon_add_global227 (value : aspis_core.field.QM31) (sums : Array Std.U64 4#usize) :
    Success (reference_poseidon.add_global227 value sums) := by
  unfold reference_poseidon.add_global227
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro limbs
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply bind
  · exact ok _
  intro i1
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply bind
  · exact ok _
  intro i3
  apply bind
  · apply index <;> scalar_tac
  intro i4
  apply bind
  · exact ok _
  intro i5
  apply bind
  · apply index <;> scalar_tac
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
  · apply index <;> scalar_tac
  intro i10
  apply bind
  · exact ok _
  intro i11
  apply bind
  · apply index <;> scalar_tac
  intro i12
  apply bind
  · exact ok _
  intro i13
  apply bind
  · apply index <;> scalar_tac
  intro i14
  apply bind
  · exact ok _
  intro i15
  apply total_reference_poseidon_extension_from_raw_limbs

#print axioms total_reference_poseidon_add_global227

theorem total_reference_poseidon_global_sums227 (state : Array aspis_core.field.QM31 16#usize) :
    Success (reference_poseidon.global_sums227 state) := by
  delta reference_poseidon.global_sums227
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply bind
  · exact ok _
  intro i1
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a1
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply bind
  · exact ok _
  intro i3
  apply bind
  · exact ok _
  intro i4
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a2
  apply bind
  · apply index <;> scalar_tac
  intro i5
  apply bind
  · exact ok _
  intro i6
  apply bind
  · exact ok _
  intro i7
  apply bind
  · apply index <;> scalar_tac
  intro q3
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a3
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply bind
  · exact ok _
  intro i9
  apply bind
  · exact ok _
  intro i10
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a4
  apply bind
  · apply index <;> scalar_tac
  intro i11
  apply bind
  · exact ok _
  intro i12
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a5
  apply bind
  · apply index <;> scalar_tac
  intro i13
  apply bind
  · exact ok _
  intro i14
  apply bind
  · exact ok _
  intro i15
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a6
  apply bind
  · apply index <;> scalar_tac
  intro i16
  apply bind
  · exact ok _
  intro i17
  apply bind
  · exact ok _
  intro i18
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a7
  apply bind
  · apply index <;> scalar_tac
  intro i19
  apply bind
  · exact ok _
  intro i20
  apply bind
  · exact ok _
  intro i21
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a8
  apply bind
  · apply index <;> scalar_tac
  intro i22
  apply bind
  · exact ok _
  intro i23
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a9
  apply bind
  · apply index <;> scalar_tac
  intro i24
  apply bind
  · exact ok _
  intro i25
  apply bind
  · exact ok _
  intro i26
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a10
  apply bind
  · apply index <;> scalar_tac
  intro i27
  apply bind
  · exact ok _
  intro i28
  apply bind
  · exact ok _
  intro i29
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a11
  apply bind
  · apply index <;> scalar_tac
  intro i30
  apply bind
  · exact ok _
  intro i31
  apply bind
  · exact ok _
  intro i32
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a12
  apply bind
  · apply index <;> scalar_tac
  intro i33
  apply bind
  · exact ok _
  intro i34
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a13
  apply bind
  · apply index <;> scalar_tac
  intro i35
  apply bind
  · exact ok _
  intro i36
  apply bind
  · exact ok _
  intro i37
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a14
  apply bind
  · apply index <;> scalar_tac
  intro i38
  apply bind
  · exact ok _
  intro i39
  apply bind
  · exact ok _
  intro i40
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a15
  apply bind
  · apply index <;> scalar_tac
  intro i41
  apply bind
  · exact ok _
  intro i42
  apply bind
  · exact ok _
  intro i43
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a16
  apply bind
  · apply index <;> scalar_tac
  intro i44
  apply bind
  · exact ok _
  intro i45
  apply bind
  · apply index <;> scalar_tac
  intro q5
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a17
  apply bind
  · apply index <;> scalar_tac
  intro i46
  apply bind
  · exact ok _
  intro i47
  apply bind
  · exact ok _
  intro i48
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a18
  apply bind
  · apply index <;> scalar_tac
  intro i49
  apply bind
  · exact ok _
  intro i50
  apply bind
  · exact ok _
  intro i51
  apply bind
  · apply index <;> scalar_tac
  intro q7
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a19
  apply bind
  · apply index <;> scalar_tac
  intro i52
  apply bind
  · exact ok _
  intro i53
  apply bind
  · exact ok _
  intro i54
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a20
  apply bind
  · apply index <;> scalar_tac
  intro i55
  apply bind
  · exact ok _
  intro i56
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a21
  apply bind
  · apply index <;> scalar_tac
  intro i57
  apply bind
  · exact ok _
  intro i58
  apply bind
  · exact ok _
  intro i59
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a22
  apply bind
  · apply index <;> scalar_tac
  intro i60
  apply bind
  · exact ok _
  intro i61
  apply bind
  · exact ok _
  intro i62
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a23
  apply bind
  · apply index <;> scalar_tac
  intro i63
  apply bind
  · exact ok _
  intro i64
  apply bind
  · exact ok _
  intro i65
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a24
  apply bind
  · apply index <;> scalar_tac
  intro i66
  apply bind
  · exact ok _
  intro i67
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a25
  apply bind
  · apply index <;> scalar_tac
  intro i68
  apply bind
  · exact ok _
  intro i69
  apply bind
  · exact ok _
  intro i70
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a26
  apply bind
  · apply index <;> scalar_tac
  intro i71
  apply bind
  · exact ok _
  intro i72
  apply bind
  · exact ok _
  intro i73
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a27
  apply bind
  · apply index <;> scalar_tac
  intro i74
  apply bind
  · exact ok _
  intro i75
  apply bind
  · exact ok _
  intro i76
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a28
  apply bind
  · apply index <;> scalar_tac
  intro i77
  apply bind
  · exact ok _
  intro i78
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a29
  apply bind
  · apply index <;> scalar_tac
  intro i79
  apply bind
  · exact ok _
  intro i80
  apply bind
  · exact ok _
  intro i81
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a30
  apply bind
  · apply index <;> scalar_tac
  intro i82
  apply bind
  · exact ok _
  intro i83
  apply bind
  · exact ok _
  intro i84
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a31
  apply bind
  · apply index <;> scalar_tac
  intro i85
  apply bind
  · exact ok _
  intro i86
  apply bind
  · exact ok _
  intro i87
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a32
  apply bind
  · apply index <;> scalar_tac
  intro i88
  apply bind
  · exact ok _
  intro i89
  apply bind
  · apply index <;> scalar_tac
  intro q9
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a33
  apply bind
  · apply index <;> scalar_tac
  intro i90
  apply bind
  · exact ok _
  intro i91
  apply bind
  · exact ok _
  intro i92
  apply bind
  · apply index <;> scalar_tac
  intro q10
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a34
  apply bind
  · apply index <;> scalar_tac
  intro i93
  apply bind
  · exact ok _
  intro i94
  apply bind
  · exact ok _
  intro i95
  apply bind
  · apply index <;> scalar_tac
  intro q11
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a35
  apply bind
  · apply index <;> scalar_tac
  intro i96
  apply bind
  · exact ok _
  intro i97
  apply bind
  · exact ok _
  intro i98
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a36
  apply bind
  · apply index <;> scalar_tac
  intro i99
  apply bind
  · exact ok _
  intro i100
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a37
  apply bind
  · apply index <;> scalar_tac
  intro i101
  apply bind
  · exact ok _
  intro i102
  apply bind
  · exact ok _
  intro i103
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a38
  apply bind
  · apply index <;> scalar_tac
  intro i104
  apply bind
  · exact ok _
  intro i105
  apply bind
  · exact ok _
  intro i106
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a39
  apply bind
  · apply index <;> scalar_tac
  intro i107
  apply bind
  · exact ok _
  intro i108
  apply bind
  · exact ok _
  intro i109
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a40
  apply bind
  · apply index <;> scalar_tac
  intro i110
  apply bind
  · exact ok _
  intro i111
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a41
  apply bind
  · apply index <;> scalar_tac
  intro i112
  apply bind
  · exact ok _
  intro i113
  apply bind
  · exact ok _
  intro i114
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a42
  apply bind
  · apply index <;> scalar_tac
  intro i115
  apply bind
  · exact ok _
  intro i116
  apply bind
  · exact ok _
  intro i117
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a43
  apply bind
  · apply index <;> scalar_tac
  intro i118
  apply bind
  · exact ok _
  intro i119
  apply bind
  · exact ok _
  intro i120
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a44
  apply bind
  · apply index <;> scalar_tac
  intro i121
  apply bind
  · exact ok _
  intro i122
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a45
  apply bind
  · apply index <;> scalar_tac
  intro i123
  apply bind
  · exact ok _
  intro i124
  apply bind
  · exact ok _
  intro i125
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a46
  apply bind
  · apply index <;> scalar_tac
  intro i126
  apply bind
  · exact ok _
  intro i127
  apply bind
  · exact ok _
  intro i128
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a47
  apply bind
  · apply index <;> scalar_tac
  intro i129
  apply bind
  · exact ok _
  intro i130
  apply bind
  · exact ok _
  intro i131
  apply bind
  · apply index <;> scalar_tac
  intro q12
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a48
  apply bind
  · apply index <;> scalar_tac
  intro i132
  apply bind
  · exact ok _
  intro i133
  apply bind
  · apply index <;> scalar_tac
  intro q13
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a49
  apply bind
  · apply index <;> scalar_tac
  intro i134
  apply bind
  · exact ok _
  intro i135
  apply bind
  · exact ok _
  intro i136
  apply bind
  · apply index <;> scalar_tac
  intro q14
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a50
  apply bind
  · apply index <;> scalar_tac
  intro i137
  apply bind
  · exact ok _
  intro i138
  apply bind
  · exact ok _
  intro i139
  apply bind
  · apply index <;> scalar_tac
  intro q15
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a51
  apply bind
  · apply index <;> scalar_tac
  intro i140
  apply bind
  · exact ok _
  intro i141
  apply bind
  · exact ok _
  intro i142
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a52
  apply bind
  · apply index <;> scalar_tac
  intro i143
  apply bind
  · exact ok _
  intro i144
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a53
  apply bind
  · apply index <;> scalar_tac
  intro i145
  apply bind
  · exact ok _
  intro i146
  apply bind
  · exact ok _
  intro i147
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a54
  apply bind
  · apply index <;> scalar_tac
  intro i148
  apply bind
  · exact ok _
  intro i149
  apply bind
  · exact ok _
  intro i150
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a55
  apply bind
  · apply index <;> scalar_tac
  intro i151
  apply bind
  · exact ok _
  intro i152
  apply bind
  · exact ok _
  intro i153
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a56
  apply bind
  · apply index <;> scalar_tac
  intro i154
  apply bind
  · exact ok _
  intro i155
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a57
  apply bind
  · apply index <;> scalar_tac
  intro i156
  apply bind
  · exact ok _
  intro i157
  apply bind
  · exact ok _
  intro i158
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a58
  apply bind
  · apply index <;> scalar_tac
  intro i159
  apply bind
  · exact ok _
  intro i160
  apply bind
  · exact ok _
  intro i161
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a59
  apply bind
  · apply index <;> scalar_tac
  intro i162
  apply bind
  · exact ok _
  intro i163
  apply bind
  · exact ok _
  intro i164
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a60
  apply bind
  · apply index <;> scalar_tac
  intro i165
  apply bind
  · exact ok _
  intro i166
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a61
  apply bind
  · apply index <;> scalar_tac
  intro i167
  apply bind
  · exact ok _
  intro i168
  apply bind
  · exact ok _
  intro i169
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a62
  apply bind
  · apply index <;> scalar_tac
  intro i170
  apply bind
  · exact ok _
  intro i171
  apply bind
  · exact ok _
  intro i172
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a63
  apply bind
  · apply index <;> scalar_tac
  intro i173
  apply bind
  · exact ok _
  intro i174
  apply bind
  · exact ok _
  intro i175
  exact ok _

#print axioms total_reference_poseidon_global_sums227

end PV_B3P_Success227
