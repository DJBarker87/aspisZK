import PV_B3P_ByteScalar226V3
namespace PV_B3P_FieldResult226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error

def value (v : U32) (j : Usize) : core.result.Result U8 E :=
  if v < 2147483647#u32 then .Ok
    (UScalar.cast .U8 (U32.wrapping_shr v
      (U32.wrapping_mul 8#u32 (UScalar.cast .U32 j))))
  else .Err aspis_core.state_only_prefix.r0.Error.Public

theorem complete_result (v : U32) (j : Usize) :
    reference226.field_byte v j = .ok (value v j) := by
  by_cases h : v < 2147483647#u32
  · rw [PV_B3P_ByteScalar226V3.field_success v j h]
    simp only [value,h,↓reduceIte]
  · rw [PV_B3P_ByteScalar226V3.field_reject v j h]
    simp only [value,h,↓reduceIte]

theorem no_outer_failure (v : U32) (j : Usize) :
    ∃ r, reference226.field_byte v j = .ok r := ⟨value v j,complete_result v j⟩

#print axioms complete_result
#print axioms no_outer_failure
end PV_B3P_FieldResult226V3
