import NEG_ProductAbstraction
set_option autoImplicit false
namespace NEG_MachineProduct
open Aeneas Aeneas.Std
/-- The actual Aeneas machine primitive, rather than an independently defined
Nat function, is admitted by the product abstraction on every full word. -/
theorem u64_value (x y : U64) :
    NEG_ProductAbstraction.Product 64 x.val y.val (UScalar.wrapping_mul x y).val := by
  unfold NEG_ProductAbstraction.Product
  change (x.bv*y.bv).toNat = (x.bv.toNat*y.bv.toNat)%2^64
  exact BitVec.toNat_mul x.bv y.bv

theorem u128_value (x y : U128) :
    NEG_ProductAbstraction.Product 128 x.val y.val (UScalar.wrapping_mul x y).val := by
  unfold NEG_ProductAbstraction.Product
  change (x.bv*y.bv).toNat = (x.bv.toNat*y.bv.toNat)%2^128
  exact BitVec.toNat_mul x.bv y.bv

#print axioms u64_value
#print axioms u128_value
end NEG_MachineProduct
