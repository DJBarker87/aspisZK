import PV_B3P_InternalSuccess227
import PV_B3P_P227_05
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_poseidon_full_round (state : Array aspis_core.field.QM31 16#usize) (constants1 : Array aspis_core.field.QM31 16#usize) :
    Success (reference_poseidon.full_round state constants1) := by
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
  · apply total_reference_poseidon_pow5
  intro q3
  apply bind
  · apply update <;> scalar_tac
  intro state1
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply index <;> scalar_tac
  intro q5
  apply bind
  · apply qadd
  intro q6
  apply bind
  · apply total_reference_poseidon_pow5
  intro q7
  apply bind
  · apply update <;> scalar_tac
  intro state2
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply index <;> scalar_tac
  intro q9
  apply bind
  · apply qadd
  intro q10
  apply bind
  · apply total_reference_poseidon_pow5
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
  · apply total_reference_poseidon_pow5
  intro q15
  apply bind
  · apply update <;> scalar_tac
  intro state4
  apply bind
  · apply index <;> scalar_tac
  intro q16
  apply bind
  · apply index <;> scalar_tac
  intro q17
  apply bind
  · apply qadd
  intro q18
  apply bind
  · apply total_reference_poseidon_pow5
  intro q19
  apply bind
  · apply update <;> scalar_tac
  intro state5
  apply bind
  · apply index <;> scalar_tac
  intro q20
  apply bind
  · apply index <;> scalar_tac
  intro q21
  apply bind
  · apply qadd
  intro q22
  apply bind
  · apply total_reference_poseidon_pow5
  intro q23
  apply bind
  · apply update <;> scalar_tac
  intro state6
  apply bind
  · apply index <;> scalar_tac
  intro q24
  apply bind
  · apply index <;> scalar_tac
  intro q25
  apply bind
  · apply qadd
  intro q26
  apply bind
  · apply total_reference_poseidon_pow5
  intro q27
  apply bind
  · apply update <;> scalar_tac
  intro state7
  apply bind
  · apply index <;> scalar_tac
  intro q28
  apply bind
  · apply index <;> scalar_tac
  intro q29
  apply bind
  · apply qadd
  intro q30
  apply bind
  · apply total_reference_poseidon_pow5
  intro q31
  apply bind
  · apply update <;> scalar_tac
  intro state8
  apply bind
  · apply index <;> scalar_tac
  intro q32
  apply bind
  · apply index <;> scalar_tac
  intro q33
  apply bind
  · apply qadd
  intro q34
  apply bind
  · apply total_reference_poseidon_pow5
  intro q35
  apply bind
  · apply update <;> scalar_tac
  intro state9
  apply bind
  · apply index <;> scalar_tac
  intro q36
  apply bind
  · apply index <;> scalar_tac
  intro q37
  apply bind
  · apply qadd
  intro q38
  apply bind
  · apply total_reference_poseidon_pow5
  intro q39
  apply bind
  · apply update <;> scalar_tac
  intro state10
  apply bind
  · apply index <;> scalar_tac
  intro q40
  apply bind
  · apply index <;> scalar_tac
  intro q41
  apply bind
  · apply qadd
  intro q42
  apply bind
  · apply total_reference_poseidon_pow5
  intro q43
  apply bind
  · apply update <;> scalar_tac
  intro state11
  apply bind
  · apply index <;> scalar_tac
  intro q44
  apply bind
  · apply index <;> scalar_tac
  intro q45
  apply bind
  · apply qadd
  intro q46
  apply bind
  · apply total_reference_poseidon_pow5
  intro q47
  apply bind
  · apply update <;> scalar_tac
  intro state12
  apply bind
  · apply index <;> scalar_tac
  intro q48
  apply bind
  · apply index <;> scalar_tac
  intro q49
  apply bind
  · apply qadd
  intro q50
  apply bind
  · apply total_reference_poseidon_pow5
  intro q51
  apply bind
  · apply update <;> scalar_tac
  intro state13
  apply bind
  · apply index <;> scalar_tac
  intro q52
  apply bind
  · apply index <;> scalar_tac
  intro q53
  apply bind
  · apply qadd
  intro q54
  apply bind
  · apply total_reference_poseidon_pow5
  intro q55
  apply bind
  · apply update <;> scalar_tac
  intro state14
  apply bind
  · apply index <;> scalar_tac
  intro q56
  apply bind
  · apply index <;> scalar_tac
  intro q57
  apply bind
  · apply qadd
  intro q58
  apply bind
  · apply total_reference_poseidon_pow5
  intro q59
  apply bind
  · apply update <;> scalar_tac
  intro state15
  apply bind
  · apply index <;> scalar_tac
  intro q60
  apply bind
  · apply index <;> scalar_tac
  intro q61
  apply bind
  · apply qadd
  intro q62
  apply bind
  · apply total_reference_poseidon_pow5
  intro q63
  apply bind
  · apply update <;> scalar_tac
  intro state16
  apply total_reference_poseidon_external_linear_lazy

#print axioms total_reference_poseidon_full_round

theorem total_reference_poseidon_full_round_m31_constants (state : Array aspis_core.field.QM31 16#usize) (constants1 : Array Std.U32 16#usize) :
    Success (reference_poseidon.full_round_m31_constants state constants1) := by
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply bind
  · apply add
  intro m
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q1, index_mut_back⟩
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply total_reference_poseidon_pow5
  intro q3
  apply bind
  · apply update <;> scalar_tac
  intro state2
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply index <;> scalar_tac
  intro i1
  apply bind
  · apply add
  intro m1
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q5, index_mut_back1⟩
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply bind
  · apply total_reference_poseidon_pow5
  intro q7
  apply bind
  · apply update <;> scalar_tac
  intro state4
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply bind
  · apply add
  intro m2
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q9, index_mut_back2⟩
  apply bind
  · apply index <;> scalar_tac
  intro q10
  apply bind
  · apply total_reference_poseidon_pow5
  intro q11
  apply bind
  · apply update <;> scalar_tac
  intro state6
  apply bind
  · apply index <;> scalar_tac
  intro q12
  apply bind
  · apply index <;> scalar_tac
  intro i3
  apply bind
  · apply add
  intro m3
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q13, index_mut_back3⟩
  apply bind
  · apply index <;> scalar_tac
  intro q14
  apply bind
  · apply total_reference_poseidon_pow5
  intro q15
  apply bind
  · apply update <;> scalar_tac
  intro state8
  apply bind
  · apply index <;> scalar_tac
  intro q16
  apply bind
  · apply index <;> scalar_tac
  intro i4
  apply bind
  · apply add
  intro m4
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q17, index_mut_back4⟩
  apply bind
  · apply index <;> scalar_tac
  intro q18
  apply bind
  · apply total_reference_poseidon_pow5
  intro q19
  apply bind
  · apply update <;> scalar_tac
  intro state10
  apply bind
  · apply index <;> scalar_tac
  intro q20
  apply bind
  · apply index <;> scalar_tac
  intro i5
  apply bind
  · apply add
  intro m5
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q21, index_mut_back5⟩
  apply bind
  · apply index <;> scalar_tac
  intro q22
  apply bind
  · apply total_reference_poseidon_pow5
  intro q23
  apply bind
  · apply update <;> scalar_tac
  intro state12
  apply bind
  · apply index <;> scalar_tac
  intro q24
  apply bind
  · apply index <;> scalar_tac
  intro i6
  apply bind
  · apply add
  intro m6
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q25, index_mut_back6⟩
  apply bind
  · apply index <;> scalar_tac
  intro q26
  apply bind
  · apply total_reference_poseidon_pow5
  intro q27
  apply bind
  · apply update <;> scalar_tac
  intro state14
  apply bind
  · apply index <;> scalar_tac
  intro q28
  apply bind
  · apply index <;> scalar_tac
  intro i7
  apply bind
  · apply add
  intro m7
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q29, index_mut_back7⟩
  apply bind
  · apply index <;> scalar_tac
  intro q30
  apply bind
  · apply total_reference_poseidon_pow5
  intro q31
  apply bind
  · apply update <;> scalar_tac
  intro state16
  apply bind
  · apply index <;> scalar_tac
  intro q32
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply bind
  · apply add
  intro m8
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q33, index_mut_back8⟩
  apply bind
  · apply index <;> scalar_tac
  intro q34
  apply bind
  · apply total_reference_poseidon_pow5
  intro q35
  apply bind
  · apply update <;> scalar_tac
  intro state18
  apply bind
  · apply index <;> scalar_tac
  intro q36
  apply bind
  · apply index <;> scalar_tac
  intro i9
  apply bind
  · apply add
  intro m9
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q37, index_mut_back9⟩
  apply bind
  · apply index <;> scalar_tac
  intro q38
  apply bind
  · apply total_reference_poseidon_pow5
  intro q39
  apply bind
  · apply update <;> scalar_tac
  intro state20
  apply bind
  · apply index <;> scalar_tac
  intro q40
  apply bind
  · apply index <;> scalar_tac
  intro i10
  apply bind
  · apply add
  intro m10
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q41, index_mut_back10⟩
  apply bind
  · apply index <;> scalar_tac
  intro q42
  apply bind
  · apply total_reference_poseidon_pow5
  intro q43
  apply bind
  · apply update <;> scalar_tac
  intro state22
  apply bind
  · apply index <;> scalar_tac
  intro q44
  apply bind
  · apply index <;> scalar_tac
  intro i11
  apply bind
  · apply add
  intro m11
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q45, index_mut_back11⟩
  apply bind
  · apply index <;> scalar_tac
  intro q46
  apply bind
  · apply total_reference_poseidon_pow5
  intro q47
  apply bind
  · apply update <;> scalar_tac
  intro state24
  apply bind
  · apply index <;> scalar_tac
  intro q48
  apply bind
  · apply index <;> scalar_tac
  intro i12
  apply bind
  · apply add
  intro m12
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q49, index_mut_back12⟩
  apply bind
  · apply index <;> scalar_tac
  intro q50
  apply bind
  · apply total_reference_poseidon_pow5
  intro q51
  apply bind
  · apply update <;> scalar_tac
  intro state26
  apply bind
  · apply index <;> scalar_tac
  intro q52
  apply bind
  · apply index <;> scalar_tac
  intro i13
  apply bind
  · apply add
  intro m13
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q53, index_mut_back13⟩
  apply bind
  · apply index <;> scalar_tac
  intro q54
  apply bind
  · apply total_reference_poseidon_pow5
  intro q55
  apply bind
  · apply update <;> scalar_tac
  intro state28
  apply bind
  · apply index <;> scalar_tac
  intro q56
  apply bind
  · apply index <;> scalar_tac
  intro i14
  apply bind
  · apply add
  intro m14
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q57, index_mut_back14⟩
  apply bind
  · apply index <;> scalar_tac
  intro q58
  apply bind
  · apply total_reference_poseidon_pow5
  intro q59
  apply bind
  · apply update <;> scalar_tac
  intro state30
  apply bind
  · apply index <;> scalar_tac
  intro q60
  apply bind
  · apply index <;> scalar_tac
  intro i15
  apply bind
  · apply add
  intro m15
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q61, index_mut_back15⟩
  apply bind
  · apply index <;> scalar_tac
  intro q62
  apply bind
  · apply total_reference_poseidon_pow5
  intro q63
  apply bind
  · apply update <;> scalar_tac
  intro state32
  apply total_reference_poseidon_external_linear_lazy

#print axioms total_reference_poseidon_full_round_m31_constants

theorem total_reference_poseidon_full_round_packed (state : Array aspis_core.field.QM31 16#usize) (constants1 : Array aspis_core.field.QM31 16#usize) :
    Success (reference_poseidon.full_round_packed state constants1) := by
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
  · apply total_reference_poseidon_pow5
  intro q3
  apply bind
  · apply update <;> scalar_tac
  intro state1
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply index <;> scalar_tac
  intro q5
  apply bind
  · apply qadd
  intro q6
  apply bind
  · apply total_reference_poseidon_pow5
  intro q7
  apply bind
  · apply update <;> scalar_tac
  intro state2
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply index <;> scalar_tac
  intro q9
  apply bind
  · apply qadd
  intro q10
  apply bind
  · apply total_reference_poseidon_pow5
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
  · apply total_reference_poseidon_pow5
  intro q15
  apply bind
  · apply update <;> scalar_tac
  intro state4
  apply bind
  · apply index <;> scalar_tac
  intro q16
  apply bind
  · apply index <;> scalar_tac
  intro q17
  apply bind
  · apply qadd
  intro q18
  apply bind
  · apply total_reference_poseidon_pow5
  intro q19
  apply bind
  · apply update <;> scalar_tac
  intro state5
  apply bind
  · apply index <;> scalar_tac
  intro q20
  apply bind
  · apply index <;> scalar_tac
  intro q21
  apply bind
  · apply qadd
  intro q22
  apply bind
  · apply total_reference_poseidon_pow5
  intro q23
  apply bind
  · apply update <;> scalar_tac
  intro state6
  apply bind
  · apply index <;> scalar_tac
  intro q24
  apply bind
  · apply index <;> scalar_tac
  intro q25
  apply bind
  · apply qadd
  intro q26
  apply bind
  · apply total_reference_poseidon_pow5
  intro q27
  apply bind
  · apply update <;> scalar_tac
  intro state7
  apply bind
  · apply index <;> scalar_tac
  intro q28
  apply bind
  · apply index <;> scalar_tac
  intro q29
  apply bind
  · apply qadd
  intro q30
  apply bind
  · apply total_reference_poseidon_pow5
  intro q31
  apply bind
  · apply update <;> scalar_tac
  intro state8
  apply bind
  · apply index <;> scalar_tac
  intro q32
  apply bind
  · apply index <;> scalar_tac
  intro q33
  apply bind
  · apply qadd
  intro q34
  apply bind
  · apply total_reference_poseidon_pow5
  intro q35
  apply bind
  · apply update <;> scalar_tac
  intro state9
  apply bind
  · apply index <;> scalar_tac
  intro q36
  apply bind
  · apply index <;> scalar_tac
  intro q37
  apply bind
  · apply qadd
  intro q38
  apply bind
  · apply total_reference_poseidon_pow5
  intro q39
  apply bind
  · apply update <;> scalar_tac
  intro state10
  apply bind
  · apply index <;> scalar_tac
  intro q40
  apply bind
  · apply index <;> scalar_tac
  intro q41
  apply bind
  · apply qadd
  intro q42
  apply bind
  · apply total_reference_poseidon_pow5
  intro q43
  apply bind
  · apply update <;> scalar_tac
  intro state11
  apply bind
  · apply index <;> scalar_tac
  intro q44
  apply bind
  · apply index <;> scalar_tac
  intro q45
  apply bind
  · apply qadd
  intro q46
  apply bind
  · apply total_reference_poseidon_pow5
  intro q47
  apply bind
  · apply update <;> scalar_tac
  intro state12
  apply bind
  · apply index <;> scalar_tac
  intro q48
  apply bind
  · apply index <;> scalar_tac
  intro q49
  apply bind
  · apply qadd
  intro q50
  apply bind
  · apply total_reference_poseidon_pow5
  intro q51
  apply bind
  · apply update <;> scalar_tac
  intro state13
  apply bind
  · apply index <;> scalar_tac
  intro q52
  apply bind
  · apply index <;> scalar_tac
  intro q53
  apply bind
  · apply qadd
  intro q54
  apply bind
  · apply total_reference_poseidon_pow5
  intro q55
  apply bind
  · apply update <;> scalar_tac
  intro state14
  apply bind
  · apply index <;> scalar_tac
  intro q56
  apply bind
  · apply index <;> scalar_tac
  intro q57
  apply bind
  · apply qadd
  intro q58
  apply bind
  · apply total_reference_poseidon_pow5
  intro q59
  apply bind
  · apply update <;> scalar_tac
  intro state15
  apply bind
  · apply index <;> scalar_tac
  intro q60
  apply bind
  · apply index <;> scalar_tac
  intro q61
  apply bind
  · apply qadd
  intro q62
  apply bind
  · apply total_reference_poseidon_pow5
  intro q63
  apply bind
  · apply update <;> scalar_tac
  intro state16
  apply total_reference_poseidon_external_linear_packed

#print axioms total_reference_poseidon_full_round_packed

theorem total_reference_poseidon_full_round_m31_constants_packed (state : Array aspis_core.field.QM31 16#usize) (constants1 : Array Std.U32 16#usize) :
    Success (reference_poseidon.full_round_m31_constants_packed state constants1) := by
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply bind
  · apply add
  intro m
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q1, index_mut_back⟩
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply total_reference_poseidon_pow5
  intro q3
  apply bind
  · apply update <;> scalar_tac
  intro state2
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply index <;> scalar_tac
  intro i1
  apply bind
  · apply add
  intro m1
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q5, index_mut_back1⟩
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply bind
  · apply total_reference_poseidon_pow5
  intro q7
  apply bind
  · apply update <;> scalar_tac
  intro state4
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply bind
  · apply add
  intro m2
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q9, index_mut_back2⟩
  apply bind
  · apply index <;> scalar_tac
  intro q10
  apply bind
  · apply total_reference_poseidon_pow5
  intro q11
  apply bind
  · apply update <;> scalar_tac
  intro state6
  apply bind
  · apply index <;> scalar_tac
  intro q12
  apply bind
  · apply index <;> scalar_tac
  intro i3
  apply bind
  · apply add
  intro m3
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q13, index_mut_back3⟩
  apply bind
  · apply index <;> scalar_tac
  intro q14
  apply bind
  · apply total_reference_poseidon_pow5
  intro q15
  apply bind
  · apply update <;> scalar_tac
  intro state8
  apply bind
  · apply index <;> scalar_tac
  intro q16
  apply bind
  · apply index <;> scalar_tac
  intro i4
  apply bind
  · apply add
  intro m4
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q17, index_mut_back4⟩
  apply bind
  · apply index <;> scalar_tac
  intro q18
  apply bind
  · apply total_reference_poseidon_pow5
  intro q19
  apply bind
  · apply update <;> scalar_tac
  intro state10
  apply bind
  · apply index <;> scalar_tac
  intro q20
  apply bind
  · apply index <;> scalar_tac
  intro i5
  apply bind
  · apply add
  intro m5
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q21, index_mut_back5⟩
  apply bind
  · apply index <;> scalar_tac
  intro q22
  apply bind
  · apply total_reference_poseidon_pow5
  intro q23
  apply bind
  · apply update <;> scalar_tac
  intro state12
  apply bind
  · apply index <;> scalar_tac
  intro q24
  apply bind
  · apply index <;> scalar_tac
  intro i6
  apply bind
  · apply add
  intro m6
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q25, index_mut_back6⟩
  apply bind
  · apply index <;> scalar_tac
  intro q26
  apply bind
  · apply total_reference_poseidon_pow5
  intro q27
  apply bind
  · apply update <;> scalar_tac
  intro state14
  apply bind
  · apply index <;> scalar_tac
  intro q28
  apply bind
  · apply index <;> scalar_tac
  intro i7
  apply bind
  · apply add
  intro m7
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q29, index_mut_back7⟩
  apply bind
  · apply index <;> scalar_tac
  intro q30
  apply bind
  · apply total_reference_poseidon_pow5
  intro q31
  apply bind
  · apply update <;> scalar_tac
  intro state16
  apply bind
  · apply index <;> scalar_tac
  intro q32
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply bind
  · apply add
  intro m8
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q33, index_mut_back8⟩
  apply bind
  · apply index <;> scalar_tac
  intro q34
  apply bind
  · apply total_reference_poseidon_pow5
  intro q35
  apply bind
  · apply update <;> scalar_tac
  intro state18
  apply bind
  · apply index <;> scalar_tac
  intro q36
  apply bind
  · apply index <;> scalar_tac
  intro i9
  apply bind
  · apply add
  intro m9
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q37, index_mut_back9⟩
  apply bind
  · apply index <;> scalar_tac
  intro q38
  apply bind
  · apply total_reference_poseidon_pow5
  intro q39
  apply bind
  · apply update <;> scalar_tac
  intro state20
  apply bind
  · apply index <;> scalar_tac
  intro q40
  apply bind
  · apply index <;> scalar_tac
  intro i10
  apply bind
  · apply add
  intro m10
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q41, index_mut_back10⟩
  apply bind
  · apply index <;> scalar_tac
  intro q42
  apply bind
  · apply total_reference_poseidon_pow5
  intro q43
  apply bind
  · apply update <;> scalar_tac
  intro state22
  apply bind
  · apply index <;> scalar_tac
  intro q44
  apply bind
  · apply index <;> scalar_tac
  intro i11
  apply bind
  · apply add
  intro m11
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q45, index_mut_back11⟩
  apply bind
  · apply index <;> scalar_tac
  intro q46
  apply bind
  · apply total_reference_poseidon_pow5
  intro q47
  apply bind
  · apply update <;> scalar_tac
  intro state24
  apply bind
  · apply index <;> scalar_tac
  intro q48
  apply bind
  · apply index <;> scalar_tac
  intro i12
  apply bind
  · apply add
  intro m12
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q49, index_mut_back12⟩
  apply bind
  · apply index <;> scalar_tac
  intro q50
  apply bind
  · apply total_reference_poseidon_pow5
  intro q51
  apply bind
  · apply update <;> scalar_tac
  intro state26
  apply bind
  · apply index <;> scalar_tac
  intro q52
  apply bind
  · apply index <;> scalar_tac
  intro i13
  apply bind
  · apply add
  intro m13
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q53, index_mut_back13⟩
  apply bind
  · apply index <;> scalar_tac
  intro q54
  apply bind
  · apply total_reference_poseidon_pow5
  intro q55
  apply bind
  · apply update <;> scalar_tac
  intro state28
  apply bind
  · apply index <;> scalar_tac
  intro q56
  apply bind
  · apply index <;> scalar_tac
  intro i14
  apply bind
  · apply add
  intro m14
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q57, index_mut_back14⟩
  apply bind
  · apply index <;> scalar_tac
  intro q58
  apply bind
  · apply total_reference_poseidon_pow5
  intro q59
  apply bind
  · apply update <;> scalar_tac
  intro state30
  apply bind
  · apply index <;> scalar_tac
  intro q60
  apply bind
  · apply index <;> scalar_tac
  intro i15
  apply bind
  · apply add
  intro m15
  apply bind
  · apply borrow <;> scalar_tac
  rintro ⟨q61, index_mut_back15⟩
  apply bind
  · apply index <;> scalar_tac
  intro q62
  apply bind
  · apply total_reference_poseidon_pow5
  intro q63
  apply bind
  · apply update <;> scalar_tac
  intro state32
  apply total_reference_poseidon_external_linear_packed

#print axioms total_reference_poseidon_full_round_m31_constants_packed

end PV_B3P_Success227
