import RPu_AspisR1_PoseidonPreparedChannelRowProduct

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedRowSumAlgebra
open AspisV8R15.ExactTowerBase

abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact

theorem rowModel_sum3 (a0 a1 a2 b0 b1 b2 c0 c1 c2 : M) :
    (⟨(a0+a1+a2) - (b0+b1+b2),
      (c0+c1+c2) - (a0+a1+a2) - (b0+b1+b2)⟩ : CMExact) =
      (⟨a0-b0, c0-a0-b0⟩ : CMExact) +
      ⟨a1-b1, c1-a1-b1⟩ + ⟨a2-b2, c2-a2-b2⟩ := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_add]
    ring
  · simp only [QuadraticAlgebra.im_add]
    ring

#print axioms rowModel_sum3
end AspisR1.PoseidonPreparedRowSumAlgebra
