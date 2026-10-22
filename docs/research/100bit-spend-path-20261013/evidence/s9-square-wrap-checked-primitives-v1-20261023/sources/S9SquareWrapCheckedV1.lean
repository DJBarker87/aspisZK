import ExtractedMaskReducerOps
import R22TotalUnsignedPrimitives
import S9U64ScalarCompatibilityV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9SquareWrapCheckedV1

abbrev U64 := UScalar UScalarTy.U64

theorem u64_wrapping_sub_eq_uscalar (x y : U64) :
    Std.U64.wrapping_sub x y = UScalar.wrapping_sub x y := by
  apply UScalar.eq_of_val_eq
  rw [Std.U64.wrapping_sub_val_eq, UScalar.wrapping_sub_val_eq]

theorem wrapping_add_eq_checked (x y : U64)
    (h : x.val + y.val < 2^64) :
    lift (Std.U64.wrapping_add x y) = UScalar.add x y := by
  obtain ⟨z, hz, _hv⟩ := AspisR1.ExtractedMaskReducerOps.add_success x y h
  have hw := (AspisR1.R22TotalUnsignedPrimitives.add_success x y z hz).1
  change Result.ok (Std.U64.wrapping_add x y) = UScalar.add x y
  rw [AspisR1S9U64ScalarCompatibilityV1.u64_wrapping_add_eq_uscalar, hw]
  exact hz.symm

theorem wrapping_sub_eq_checked (x y : U64)
    (h : y.val ≤ x.val) :
    lift (Std.U64.wrapping_sub x y) = UScalar.sub x y := by
  obtain ⟨z, hz, _hv⟩ := AspisR1.ExtractedMaskReducerOps.sub_success x y h
  have hw := (AspisR1.R22TotalUnsignedPrimitives.sub_success x y z hz).1
  change Result.ok (Std.U64.wrapping_sub x y) = UScalar.sub x y
  rw [u64_wrapping_sub_eq_uscalar, hw]
  exact hz.symm

theorem wrapping_mul_eq_checked (x y : U64)
    (h : x.val * y.val < 2^64) :
    lift (Std.U64.wrapping_mul x y) = UScalar.mul x y := by
  obtain ⟨z, hz, _hv⟩ := AspisR1.ExtractedMaskReducerOps.mul_success x y h
  have hw := (AspisR1.R22TotalUnsignedPrimitives.mul_success x y z hz).1
  change Result.ok (Std.U64.wrapping_mul x y) = UScalar.mul x y
  rw [AspisR1S9U64ScalarCompatibilityV1.u64_wrapping_mul_eq_uscalar, hw]
  exact hz.symm

#print axioms u64_wrapping_sub_eq_uscalar
#print axioms wrapping_add_eq_checked
#print axioms wrapping_sub_eq_checked
#print axioms wrapping_mul_eq_checked

end AspisR1S9SquareWrapCheckedV1
