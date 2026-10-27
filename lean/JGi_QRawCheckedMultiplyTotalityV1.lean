import Aeneas

set_option autoImplicit false
open Aeneas Aeneas.Std Result WP

namespace AspisR1S5QRawTotality

abbrev U64 := UScalar UScalarTy.U64

/-- A checked U64 product succeeds whenever its mathematical product fits the
source integer type. The returned scalar is the exact product. -/
theorem u64_mul_total_of_le (x y : U64)
    (hmax : x.val * y.val ≤ UScalar.max UScalarTy.U64) :
    ∃ z : U64, UScalar.mul x y = .ok z ∧ z.val = x.val * y.val := by
  have hspec : UScalar.mul x y ⦃z => z.val = x.val * y.val⦄ := by
    apply UScalar.mul_spec (x := x) (y := y)
    exact hmax
  exact WP.spec_imp_exists hspec

end AspisR1S5QRawTotality

#print axioms AspisR1S5QRawTotality.u64_mul_total_of_le
