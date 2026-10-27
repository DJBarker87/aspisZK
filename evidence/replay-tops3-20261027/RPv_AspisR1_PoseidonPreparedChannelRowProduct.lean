import RPv_AspisR1_PoseidonPreparedChannelRowValue

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedChannelRowProduct
open Aeneas.Std AspisV8R15.ExactTowerBase

abbrev U64 := UScalar UScalarTy.U64
abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact

/-- The Karatsuba row decoder is exactly multiplication in the quadratic
extension when its three channels are the two diagonal products and their
pairwise-sum product. -/
theorem rowModel_mul (a b c d : M) (r0 r1 r2 : U64)
    (h0 : (r0.val : M) = a * c)
    (h1 : (r1.val : M) = b * d)
    (h2 : (r2.val : M) = (a + b) * (c + d)) :
    AspisR1.PoseidonPreparedChannelRowValue.rowModel r0 r1 r2 =
      (⟨a * c - b * d, a * d + b * c⟩ : CMExact) := by
  apply QuadraticAlgebra.ext
  · change (r0.val : M) - (r1.val : M) = a * c - b * d
    rw [h0, h1]
  · change (r2.val : M) - (r0.val : M) - (r1.val : M) = a * d + b * c
    rw [h2, h0, h1]
    ring

#print axioms rowModel_mul
end AspisR1.PoseidonPreparedChannelRowProduct
