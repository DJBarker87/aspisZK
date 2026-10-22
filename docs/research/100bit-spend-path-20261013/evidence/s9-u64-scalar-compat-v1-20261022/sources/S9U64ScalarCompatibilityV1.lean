import Aeneas

set_option autoImplicit false

namespace AspisR1S9U64ScalarCompatibilityV1

open Aeneas.Std

/-- The specialized U64 library theorem and the generic UScalar theorem give
    the same modulo value, hence the same machine word. This is for arbitrary
    inputs, including overflow. -/
theorem u64_wrapping_add_eq_uscalar (x y : U64) :
    U64.wrapping_add x y = UScalar.wrapping_add x y := by
  apply UScalar.eq_of_val_eq
  calc
    (U64.wrapping_add x y).val = (x.val + y.val) % UScalar.size .U64 :=
      U64.wrapping_add_val_eq x y
    _ = (UScalar.wrapping_add x y).val :=
      (UScalar.wrapping_add_val_eq x y).symm

/-- Multiplication has the same specialization compatibility, including
    arbitrary overflowing inputs. -/
theorem u64_wrapping_mul_eq_uscalar (x y : U64) :
    U64.wrapping_mul x y = UScalar.wrapping_mul x y := by
  apply UScalar.eq_of_val_eq
  calc
    (U64.wrapping_mul x y).val = (x.val * y.val) % UScalar.size .U64 :=
      U64.wrapping_mul_val_eq x y
    _ = (UScalar.wrapping_mul x y).val :=
      (UScalar.wrapping_mul_val_eq x y).symm

/-- The U64 `&&&` notation and the generic unsigned scalar `and` operation
    agree for arbitrary operands. -/
theorem u64_and_eq_uscalar (x y : U64) :
    (x &&& y) = UScalar.and x y := by
  rfl

#print axioms AspisR1S9U64ScalarCompatibilityV1.u64_wrapping_add_eq_uscalar
#print axioms AspisR1S9U64ScalarCompatibilityV1.u64_wrapping_mul_eq_uscalar
#print axioms AspisR1S9U64ScalarCompatibilityV1.u64_and_eq_uscalar

end AspisR1S9U64ScalarCompatibilityV1
