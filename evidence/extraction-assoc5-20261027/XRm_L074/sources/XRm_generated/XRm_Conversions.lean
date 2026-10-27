import XRm_FieldValues
open Aeneas Aeneas.Std Result
namespace XRm_Conversions
theorem widen (a : U32) : core.convert.num.FromU64U32.from a=UScalar.cast .U64 a := by
  apply UScalar.eq_of_val_eq
  simp [core.convert.num.FromU64U32.from,UScalar.cast_val_eq,UScalarTy.U64_numBits_eq]
  have ha : a.val<4294967296 := by scalar_tac
  omega
#print core.convert.num.FromU64U32.from
#print axioms widen
end XRm_Conversions
