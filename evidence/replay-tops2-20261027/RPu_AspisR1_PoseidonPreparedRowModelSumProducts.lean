import RPu_AspisR1_PoseidonPreparedKaratsubaRowAlgebra
import RPu_AspisR1_PoseidonPreparedRowSumAlgebra
import RPu_AspisR1_PoseidonPreparedChannelRowValue

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedRowModelSumProducts
open Aeneas.Std AspisV8R15.ExactTowerBase

abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev U64 := UScalar UScalarTy.U64

 theorem rowModel_sum_three_products (r0 r1 r2 : U64)
    (a0 b0 a1 b1 a2 b2 c0 d0 c1 d1 c2 d2 : M)
    (h0 : (r0.val : M) = a0*c0 + a1*c1 + a2*c2)
    (h1 : (r1.val : M) = b0*d0 + b1*d1 + b2*d2)
    (h2 : (r2.val : M) = (a0+b0)*(c0+d0) + (a1+b1)*(c1+d1) +
      (a2+b2)*(c2+d2)) :
    AspisR1.PoseidonPreparedChannelRowValue.rowModel r0 r1 r2 =
      (⟨a0,b0⟩ : CMExact) * ⟨c0,d0⟩ +
      (⟨a1,b1⟩ : CMExact) * ⟨c1,d1⟩ +
      (⟨a2,b2⟩ : CMExact) * ⟨c2,d2⟩ := by
  calc
    AspisR1.PoseidonPreparedChannelRowValue.rowModel r0 r1 r2 =
        (⟨a0*c0-b0*d0, (a0+b0)*(c0+d0)-a0*c0-b0*d0⟩ : CMExact) +
        ⟨a1*c1-b1*d1, (a1+b1)*(c1+d1)-a1*c1-b1*d1⟩ +
        ⟨a2*c2-b2*d2, (a2+b2)*(c2+d2)-a2*c2-b2*d2⟩ := by
      change (⟨(r0.val : M) - (r1.val : M),
        (r2.val : M) - (r0.val : M) - (r1.val : M)⟩ : CMExact) = _
      rw [h0, h1, h2]
      exact AspisR1.PoseidonPreparedRowSumAlgebra.rowModel_sum3
        (a0*c0) (a1*c1) (a2*c2) (b0*d0) (b1*d1) (b2*d2)
        ((a0+b0)*(c0+d0)) ((a1+b1)*(c1+d1)) ((a2+b2)*(c2+d2))
    _ = _ := by
      rw [AspisR1.PoseidonPreparedKaratsubaRowAlgebra.karatsuba_row_mul,
        AspisR1.PoseidonPreparedKaratsubaRowAlgebra.karatsuba_row_mul,
        AspisR1.PoseidonPreparedKaratsubaRowAlgebra.karatsuba_row_mul]

#print axioms rowModel_sum_three_products
end AspisR1.PoseidonPreparedRowModelSumProducts
