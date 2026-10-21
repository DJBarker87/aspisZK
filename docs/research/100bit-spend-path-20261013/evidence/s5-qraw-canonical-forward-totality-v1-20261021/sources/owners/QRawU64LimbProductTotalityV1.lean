import QRawCheckedMultiplyTotalityV1

set_option autoImplicit false
open Aeneas
namespace AspisR1S5QRawCanonicalProductTotality

abbrev U64 := UScalar UScalarTy.U64

/-- The checked U64 products used on mapped canonical field limbs are total. -/
theorem u64_canonical_limb_product_total (x y : U64)
    (hx : x.val ≤ 2^31 - 2) (hy : y.val ≤ 2^31 - 2) :
    ∃ z : U64, UScalar.mul x y = .ok z ∧ z.val = x.val * y.val := by
  have hprod : x.val * y.val ≤ (2^31 - 2)^2 := Nat.mul_le_mul hx hy
  have hmax : x.val * y.val ≤ UScalar.max UScalarTy.U64 := by
    calc
      x.val * y.val ≤ (2^31 - 2)^2 := hprod
      _ ≤ 2^64 - 1 := by norm_num
      _ = UScalar.max UScalarTy.U64 := by
        rw [UScalar.max, UScalarTy.U64_numBits_eq]
  exact u64_mul_total_of_le x y hmax

#print axioms u64_canonical_limb_product_total
end AspisR1S5QRawCanonicalProductTotality
