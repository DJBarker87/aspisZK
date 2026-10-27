import XRm_FieldValues
open Aeneas Aeneas.Std Result
namespace XRm_Conversions
theorem widen (a : U32) : core.convert.num.FromU64U32.from a=UScalar.cast .U64 a := by
  apply UScalar.eq_of_val_eq
  change (BitVec.setWidth UScalarTy.U64.numBits a.bv).toNat=(UScalar.cast .U64 a).val
  rw [BitVec.toNat_setWidth,UScalar.cast_val_eq,UScalar.bv_toNat]
#print core.convert.num.FromU64U32.from
#print axioms widen
end XRm_Conversions
