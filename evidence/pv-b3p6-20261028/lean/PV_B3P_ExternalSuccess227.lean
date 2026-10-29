import PV_B3P_PoseidonCellsSuccess227
import PV_B3P_GlobalSumsSuccess227
import PV_B3P_P227_03
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_poseidon_external_group227 (state : Array aspis_core.field.QM31 4#usize) :
    Success (reference_poseidon.external_group227 state) := by
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a1
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a2
  apply bind
  · apply index <;> scalar_tac
  intro q3
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a3
  apply bind
  · apply index <;> scalar_tac
  intro a4
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro a6
  apply bind
  · apply index <;> scalar_tac
  intro i1
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro a7
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro a8
  apply bind
  · apply index <;> scalar_tac
  intro i3
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i4
  apply bind
  · apply index <;> scalar_tac
  intro i5
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i6
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i7
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i9
  apply bind
  · apply index <;> scalar_tac
  intro i10
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i11
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i12
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i13
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i14
  apply bind
  · apply index <;> scalar_tac
  intro i15
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i16
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i17
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i18
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i19
  apply bind
  · apply total_reference_poseidon_extension_from_raw_limbs
  intro q4
  apply bind
  · apply index <;> scalar_tac
  intro i20
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i21
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i22
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i23
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i24
  apply bind
  · apply index <;> scalar_tac
  intro i25
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i26
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i27
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i28
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i29
  apply bind
  · apply index <;> scalar_tac
  intro i30
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i31
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i32
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i33
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i34
  apply bind
  · apply index <;> scalar_tac
  intro i35
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i36
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i37
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i38
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i39
  apply bind
  · apply total_reference_poseidon_extension_from_raw_limbs
  intro q5
  apply bind
  · apply index <;> scalar_tac
  intro i40
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i41
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i42
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i43
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i44
  apply bind
  · apply index <;> scalar_tac
  intro i45
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i46
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i47
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i48
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i49
  apply bind
  · apply index <;> scalar_tac
  intro i50
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i51
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i52
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i53
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i54
  apply bind
  · apply index <;> scalar_tac
  intro i55
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i56
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i57
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i58
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i59
  apply bind
  · apply total_reference_poseidon_extension_from_raw_limbs
  intro q6
  apply bind
  · apply index <;> scalar_tac
  intro i60
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i61
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i62
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i63
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i64
  apply bind
  · apply index <;> scalar_tac
  intro i65
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i66
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i67
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i68
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i69
  apply bind
  · apply index <;> scalar_tac
  intro i70
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i71
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i72
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i73
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i74
  apply bind
  · apply index <;> scalar_tac
  intro i75
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i76
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i77
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i78
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i79
  apply bind
  · apply total_reference_poseidon_extension_from_raw_limbs
  intro q7
  exact ok _

#print axioms total_reference_poseidon_external_group227

theorem total_reference_poseidon_external_linear_lazy (state : Array aspis_core.field.QM31 16#usize) :
    Success (reference_poseidon.external_linear_lazy state) := by
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
  · apply total_reference_poseidon_external_group227
  intro output
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply update <;> scalar_tac
  intro state1
  apply bind
  · apply index <;> scalar_tac
  intro q5
  apply bind
  · apply update <;> scalar_tac
  intro state2
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply bind
  · apply update <;> scalar_tac
  intro state3
  apply bind
  · apply index <;> scalar_tac
  intro q7
  apply bind
  · apply update <;> scalar_tac
  intro state4
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply index <;> scalar_tac
  intro q9
  apply bind
  · apply index <;> scalar_tac
  intro q10
  apply bind
  · apply index <;> scalar_tac
  intro q11
  apply bind
  · apply total_reference_poseidon_external_group227
  intro output1
  apply bind
  · apply index <;> scalar_tac
  intro q12
  apply bind
  · apply update <;> scalar_tac
  intro state5
  apply bind
  · apply index <;> scalar_tac
  intro q13
  apply bind
  · apply update <;> scalar_tac
  intro state6
  apply bind
  · apply index <;> scalar_tac
  intro q14
  apply bind
  · apply update <;> scalar_tac
  intro state7
  apply bind
  · apply index <;> scalar_tac
  intro q15
  apply bind
  · apply update <;> scalar_tac
  intro state8
  apply bind
  · apply index <;> scalar_tac
  intro q16
  apply bind
  · apply index <;> scalar_tac
  intro q17
  apply bind
  · apply index <;> scalar_tac
  intro q18
  apply bind
  · apply index <;> scalar_tac
  intro q19
  apply bind
  · apply total_reference_poseidon_external_group227
  intro output2
  apply bind
  · apply index <;> scalar_tac
  intro q20
  apply bind
  · apply update <;> scalar_tac
  intro state9
  apply bind
  · apply index <;> scalar_tac
  intro q21
  apply bind
  · apply update <;> scalar_tac
  intro state10
  apply bind
  · apply index <;> scalar_tac
  intro q22
  apply bind
  · apply update <;> scalar_tac
  intro state11
  apply bind
  · apply index <;> scalar_tac
  intro q23
  apply bind
  · apply update <;> scalar_tac
  intro state12
  apply bind
  · apply index <;> scalar_tac
  intro q24
  apply bind
  · apply index <;> scalar_tac
  intro q25
  apply bind
  · apply index <;> scalar_tac
  intro q26
  apply bind
  · apply index <;> scalar_tac
  intro q27
  apply bind
  · apply total_reference_poseidon_external_group227
  intro output3
  apply bind
  · apply index <;> scalar_tac
  intro q28
  apply bind
  · apply update <;> scalar_tac
  intro state13
  apply bind
  · apply index <;> scalar_tac
  intro q29
  apply bind
  · apply update <;> scalar_tac
  intro state14
  apply bind
  · apply index <;> scalar_tac
  intro q30
  apply bind
  · apply update <;> scalar_tac
  intro state15
  apply bind
  · apply index <;> scalar_tac
  intro q31
  apply bind
  · apply update <;> scalar_tac
  intro state16
  apply bind
  · apply total_reference_poseidon_global_sums227
  intro sums
  apply bind
  · apply index <;> scalar_tac
  intro q32
  apply bind
  · apply index <;> scalar_tac
  intro a
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q33
  apply bind
  · apply update <;> scalar_tac
  intro state17
  apply bind
  · apply index <;> scalar_tac
  intro q34
  apply bind
  · apply index <;> scalar_tac
  intro a1
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q35
  apply bind
  · apply update <;> scalar_tac
  intro state18
  apply bind
  · apply index <;> scalar_tac
  intro q36
  apply bind
  · apply index <;> scalar_tac
  intro a2
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q37
  apply bind
  · apply update <;> scalar_tac
  intro state19
  apply bind
  · apply index <;> scalar_tac
  intro q38
  apply bind
  · apply index <;> scalar_tac
  intro a3
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q39
  apply bind
  · apply update <;> scalar_tac
  intro state20
  apply bind
  · apply index <;> scalar_tac
  intro q40
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q41
  apply bind
  · apply update <;> scalar_tac
  intro state21
  apply bind
  · apply index <;> scalar_tac
  intro q42
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q43
  apply bind
  · apply update <;> scalar_tac
  intro state22
  apply bind
  · apply index <;> scalar_tac
  intro q44
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q45
  apply bind
  · apply update <;> scalar_tac
  intro state23
  apply bind
  · apply index <;> scalar_tac
  intro q46
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q47
  apply bind
  · apply update <;> scalar_tac
  intro state24
  apply bind
  · apply index <;> scalar_tac
  intro q48
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q49
  apply bind
  · apply update <;> scalar_tac
  intro state25
  apply bind
  · apply index <;> scalar_tac
  intro q50
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q51
  apply bind
  · apply update <;> scalar_tac
  intro state26
  apply bind
  · apply index <;> scalar_tac
  intro q52
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q53
  apply bind
  · apply update <;> scalar_tac
  intro state27
  apply bind
  · apply index <;> scalar_tac
  intro q54
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q55
  apply bind
  · apply update <;> scalar_tac
  intro state28
  apply bind
  · apply index <;> scalar_tac
  intro q56
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q57
  apply bind
  · apply update <;> scalar_tac
  intro state29
  apply bind
  · apply index <;> scalar_tac
  intro q58
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q59
  apply bind
  · apply update <;> scalar_tac
  intro state30
  apply bind
  · apply index <;> scalar_tac
  intro q60
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q61
  apply bind
  · apply update <;> scalar_tac
  intro state31
  apply bind
  · apply index <;> scalar_tac
  intro q62
  apply bind
  · apply total_reference_poseidon_add_global227
  intro q63
  apply update <;> scalar_tac

#print axioms total_reference_poseidon_external_linear_lazy

theorem total_reference_poseidon_external_local_packed_raw (input : Array aspis_core.field.QM31 4#usize) :
    Success (reference_poseidon.external_local_packed_raw input) := by
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a1
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a2
  apply bind
  · apply index <;> scalar_tac
  intro q3
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro a3
  apply bind
  · apply index <;> scalar_tac
  intro a4
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro a6
  apply bind
  · apply index <;> scalar_tac
  intro i1
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro a7
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro a8
  apply bind
  · apply index <;> scalar_tac
  intro i3
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i4
  apply bind
  · apply index <;> scalar_tac
  intro i5
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i6
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i7
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i9
  apply bind
  · apply index <;> scalar_tac
  intro i10
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i11
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i12
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i13
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i14
  apply bind
  · apply index <;> scalar_tac
  intro i15
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i16
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i17
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i18
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i19
  apply bind
  · apply index <;> scalar_tac
  intro i20
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i21
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i22
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i23
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i24
  apply bind
  · apply index <;> scalar_tac
  intro i25
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i26
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i27
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i28
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i29
  apply bind
  · apply index <;> scalar_tac
  intro i30
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i31
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i32
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i33
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i34
  apply bind
  · apply index <;> scalar_tac
  intro i35
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i36
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i37
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i38
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i39
  apply bind
  · apply index <;> scalar_tac
  intro i40
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i41
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i42
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i43
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i44
  apply bind
  · apply index <;> scalar_tac
  intro i45
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i46
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i47
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i48
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i49
  apply bind
  · apply index <;> scalar_tac
  intro i50
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i51
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i52
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i53
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i54
  apply bind
  · apply index <;> scalar_tac
  intro i55
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i56
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i57
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i58
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i59
  apply bind
  · apply index <;> scalar_tac
  intro i60
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i61
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i62
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i63
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i64
  apply bind
  · apply index <;> scalar_tac
  intro i65
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i66
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i67
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i68
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i69
  apply bind
  · apply index <;> scalar_tac
  intro i70
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i71
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i72
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i73
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i74
  apply bind
  · apply index <;> scalar_tac
  intro i75
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i76
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i77
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i78
  apply lift_total
  apply bind
  · apply raw_limb_total <;> scalar_tac
  intro i79
  apply bind
  · apply index <;> scalar_tac
  intro a24
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply modulus_total
  intro i80
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro a25
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro a26
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro a27
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro _
  apply bind
  · apply index <;> scalar_tac
  intro i81
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i84
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i86
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i89
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i91
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i93
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i96
  apply bind
  · apply index <;> scalar_tac
  intro i97
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i99
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i101
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i104
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i108
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i110
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i113
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i115
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i117
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i119
  apply bind
  · apply index <;> scalar_tac
  intro i120
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i122
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i124
  apply lift_total
  exact ok _

#print axioms total_reference_poseidon_external_local_packed_raw

end PV_B3P_Success227
