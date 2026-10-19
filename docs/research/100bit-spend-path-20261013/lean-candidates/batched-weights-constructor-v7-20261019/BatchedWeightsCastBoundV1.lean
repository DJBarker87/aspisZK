import AspisR1BatchedWeightsExtraction.Funs
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace BatchedWeightsCastBoundV1
theorem u32_to_u64_bound (x : U32) : (UScalar.cast UScalarTy.U64 x).val < 2^32 := by
  have hx := x.hBounds
  change (BitVec.zeroExtend UScalarTy.U64.numBits x.bv).toNat < 2^UScalarTy.U32.numBits
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth_of_le (by decide)]
  exact hx
#print axioms u32_to_u64_bound
end BatchedWeightsCastBoundV1
