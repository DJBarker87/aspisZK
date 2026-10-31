import NEC_ScalarPorts
set_option autoImplicit false
namespace NEC_Widening
open Aeneas Aeneas.Std

theorem u32_u64 (value : U32) : (UScalar.cast .U64 value).val=value.val := by
 rw [UScalar.cast_val_eq]
 scalar_tac

theorem word_injective (a b : NEC_ScalarPorts.Word)
 (same : UScalar.cast .U64 a=UScalar.cast .U64 b) : a=b := by
 have values := congrArg UScalar.val same
 rw [u32_u64 a,u32_u64 b] at values
 exact NEC_ScalarPorts.m31_natural_injective a b values

#print axioms u32_u64
#print axioms word_injective
end NEC_Widening
