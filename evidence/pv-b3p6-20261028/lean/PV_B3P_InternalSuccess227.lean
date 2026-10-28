import PV_B3P_ExternalSuccess227
import PV_B3P_P227_04
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem total_reference_poseidon_external_local_packed (input : Array aspis_core.field.QM31 4#usize) :
    Success (reference_poseidon.external_local_packed input) := by
  apply bind
  · apply total_reference_poseidon_external_local_packed_raw
  intro a
  apply total_reference_poseidon_extension_from_raw_limbs

#print axioms total_reference_poseidon_external_local_packed

theorem total_reference_poseidon_external_linear_packed (state : Array aspis_core.field.QM31 16#usize) :
    Success (reference_poseidon.external_linear_packed state) := by
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q3
  apply bind
  · apply total_reference_poseidon_external_local_packed
  intro q4
  apply bind
  · apply update <;> scalar_tac
  intro local_packed1
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q5
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q7
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply total_reference_poseidon_external_local_packed
  intro q9
  apply bind
  · apply update <;> scalar_tac
  intro local_packed2
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q10
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q11
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q12
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q13
  apply bind
  · apply total_reference_poseidon_external_local_packed
  intro q14
  apply bind
  · apply update <;> scalar_tac
  intro local_packed3
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q15
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q16
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q17
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro q18
  apply bind
  · apply total_reference_poseidon_external_local_packed
  intro q19
  apply bind
  · apply update <;> scalar_tac
  intro local_packed4
  apply bind
  · apply index <;> scalar_tac
  intro q20
  apply bind
  · apply qadd
  intro q21
  apply bind
  · apply index <;> scalar_tac
  intro q22
  apply bind
  · apply qadd
  intro q23
  apply bind
  · apply index <;> scalar_tac
  intro q24
  apply bind
  · apply qadd
  intro q25
  apply bind
  · apply index <;> scalar_tac
  intro q26
  apply bind
  · apply qadd
  intro sum
  apply bind
  · apply qadd
  intro q27
  apply bind
  · apply qadd
  intro q28
  apply bind
  · apply qadd
  intro q29
  apply bind
  · apply qadd
  intro q30
  exact ok _

#print axioms total_reference_poseidon_external_linear_packed

theorem total_reference_poseidon_internal_shift227 (value : aspis_core.field.QM31) (full_sum : Array Std.U64 4#usize) (shift : Std.U8) :
    Success (reference_poseidon.internal_shift227 value full_sum shift) := by
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro limbs
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply bind
  · apply index <;> scalar_tac
  intro i1
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i5
  apply bind
  · apply index <;> scalar_tac
  intro i6
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i10
  apply bind
  · apply index <;> scalar_tac
  intro i11
  apply lift_total
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i15
  apply bind
  · apply index <;> scalar_tac
  intro i16
  apply lift_total
  apply lift_total
  apply lift_total
  apply total_reference_poseidon_extension_from_raw_limbs

#print axioms total_reference_poseidon_internal_shift227

theorem total_reference_poseidon_internal_zero227 (part_sum : Array Std.U64 4#usize) (old_zero : Array Std.U32 4#usize) :
    Success (reference_poseidon.internal_zero227 part_sum old_zero) := by
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i3
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i6
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i9
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i12
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i15
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i18
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i21
  apply lift_total
  apply lift_total
  apply total_reference_poseidon_extension_from_raw_limbs

#print axioms total_reference_poseidon_internal_zero227

theorem total_reference_poseidon_internal_full_sum227 (part_sum : Array Std.U64 4#usize) (old_zero : Array Std.U32 4#usize) :
    Success (reference_poseidon.internal_full_sum227 part_sum old_zero) := by
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply bind
  · apply index <;> scalar_tac
  intro i1
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i4
  apply bind
  · apply index <;> scalar_tac
  intro i5
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply bind
  · apply index <;> scalar_tac
  intro i9
  apply lift_total
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i12
  apply bind
  · apply index <;> scalar_tac
  intro i13
  apply lift_total
  apply lift_total
  exact ok _

#print axioms total_reference_poseidon_internal_full_sum227

theorem total_reference_poseidon_internal_sum227 (part_sum : Array Std.U64 4#usize) (value : aspis_core.field.QM31) :
    Success (reference_poseidon.internal_sum227 part_sum value) := by
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro limbs
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro part_sum1
  apply bind
  · apply index <;> scalar_tac
  intro i4
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i6
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro part_sum2
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i10
  apply lift_total
  apply bind
  · apply update <;> scalar_tac
  intro part_sum3
  apply bind
  · apply index <;> scalar_tac
  intro i12
  apply lift_total
  apply bind
  · apply index <;> scalar_tac
  intro i14
  apply lift_total
  apply update <;> scalar_tac

#print axioms total_reference_poseidon_internal_sum227

theorem total_reference_poseidon_internal_linear_lazy (state : Array aspis_core.field.QM31 16#usize) :
    Success (reference_poseidon.internal_linear_lazy state) := by
  apply bind
  · apply index <;> scalar_tac
  intro q
  apply bind
  · apply total_reference_poseidon_extension_limbs
  intro old_zero
  apply bind
  · apply index <;> scalar_tac
  intro q1
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum1
  apply bind
  · apply index <;> scalar_tac
  intro q2
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum2
  apply bind
  · apply index <;> scalar_tac
  intro q3
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum3
  apply bind
  · apply index <;> scalar_tac
  intro q4
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum4
  apply bind
  · apply index <;> scalar_tac
  intro q5
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum5
  apply bind
  · apply index <;> scalar_tac
  intro q6
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum6
  apply bind
  · apply index <;> scalar_tac
  intro q7
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum7
  apply bind
  · apply index <;> scalar_tac
  intro q8
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum8
  apply bind
  · apply index <;> scalar_tac
  intro q9
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum9
  apply bind
  · apply index <;> scalar_tac
  intro q10
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum10
  apply bind
  · apply index <;> scalar_tac
  intro q11
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum11
  apply bind
  · apply index <;> scalar_tac
  intro q12
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum12
  apply bind
  · apply index <;> scalar_tac
  intro q13
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum13
  apply bind
  · apply index <;> scalar_tac
  intro q14
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum14
  apply bind
  · apply index <;> scalar_tac
  intro q15
  apply bind
  · apply total_reference_poseidon_internal_sum227
  intro part_sum15
  apply bind
  · apply total_reference_poseidon_internal_full_sum227
  intro full_sum
  apply bind
  · apply total_reference_poseidon_internal_zero227
  intro q16
  apply bind
  · apply update <;> scalar_tac
  intro state1
  apply bind
  · apply index <;> scalar_tac
  intro q17
  apply bind
  · apply index <;> scalar_tac
  intro i
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q18
  apply bind
  · apply update <;> scalar_tac
  intro state2
  apply bind
  · apply index <;> scalar_tac
  intro q19
  apply bind
  · apply index <;> scalar_tac
  intro i1
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q20
  apply bind
  · apply update <;> scalar_tac
  intro state3
  apply bind
  · apply index <;> scalar_tac
  intro q21
  apply bind
  · apply index <;> scalar_tac
  intro i2
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q22
  apply bind
  · apply update <;> scalar_tac
  intro state4
  apply bind
  · apply index <;> scalar_tac
  intro q23
  apply bind
  · apply index <;> scalar_tac
  intro i3
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q24
  apply bind
  · apply update <;> scalar_tac
  intro state5
  apply bind
  · apply index <;> scalar_tac
  intro q25
  apply bind
  · apply index <;> scalar_tac
  intro i4
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q26
  apply bind
  · apply update <;> scalar_tac
  intro state6
  apply bind
  · apply index <;> scalar_tac
  intro q27
  apply bind
  · apply index <;> scalar_tac
  intro i5
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q28
  apply bind
  · apply update <;> scalar_tac
  intro state7
  apply bind
  · apply index <;> scalar_tac
  intro q29
  apply bind
  · apply index <;> scalar_tac
  intro i6
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q30
  apply bind
  · apply update <;> scalar_tac
  intro state8
  apply bind
  · apply index <;> scalar_tac
  intro q31
  apply bind
  · apply index <;> scalar_tac
  intro i7
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q32
  apply bind
  · apply update <;> scalar_tac
  intro state9
  apply bind
  · apply index <;> scalar_tac
  intro q33
  apply bind
  · apply index <;> scalar_tac
  intro i8
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q34
  apply bind
  · apply update <;> scalar_tac
  intro state10
  apply bind
  · apply index <;> scalar_tac
  intro q35
  apply bind
  · apply index <;> scalar_tac
  intro i9
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q36
  apply bind
  · apply update <;> scalar_tac
  intro state11
  apply bind
  · apply index <;> scalar_tac
  intro q37
  apply bind
  · apply index <;> scalar_tac
  intro i10
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q38
  apply bind
  · apply update <;> scalar_tac
  intro state12
  apply bind
  · apply index <;> scalar_tac
  intro q39
  apply bind
  · apply index <;> scalar_tac
  intro i11
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q40
  apply bind
  · apply update <;> scalar_tac
  intro state13
  apply bind
  · apply index <;> scalar_tac
  intro q41
  apply bind
  · apply index <;> scalar_tac
  intro i12
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q42
  apply bind
  · apply update <;> scalar_tac
  intro state14
  apply bind
  · apply index <;> scalar_tac
  intro q43
  apply bind
  · apply index <;> scalar_tac
  intro i13
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q44
  apply bind
  · apply update <;> scalar_tac
  intro state15
  apply bind
  · apply index <;> scalar_tac
  intro q45
  apply bind
  · apply index <;> scalar_tac
  intro i14
  apply bind
  · apply total_reference_poseidon_internal_shift227
  intro q46
  apply update <;> scalar_tac

#print axioms total_reference_poseidon_internal_linear_lazy

end PV_B3P_Success227
