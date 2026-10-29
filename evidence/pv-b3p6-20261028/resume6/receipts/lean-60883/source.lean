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

end PV_B3P_Success227
