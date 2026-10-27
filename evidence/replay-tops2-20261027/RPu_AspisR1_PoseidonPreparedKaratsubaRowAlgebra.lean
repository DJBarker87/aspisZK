import RPu_AspisR1_PoseidonPreparedSum3ProductAlgebra
import RPu_AspisR1_PoseidonPreparedFieldArithmetic

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedKaratsubaRowAlgebra
open AspisV8R15.ExactTowerBase

abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact

 theorem karatsuba_row_mul (a b c d : M) :
    (⟨a*c-b*d, (a+b)*(c+d)-a*c-b*d⟩ : CMExact) =
      (⟨a,b⟩ : CMExact) * ⟨c,d⟩ := by
  apply QuadraticAlgebra.ext
  · rw [QuadraticAlgebra.re_mul]
    simp [AspisV8R15.ExactTowerBase.qm31R]
    ring
  · rw [QuadraticAlgebra.im_mul]
    simp [AspisV8R15.ExactTowerBase.qm31R]
    ring

#print axioms karatsuba_row_mul
end AspisR1.PoseidonPreparedKaratsubaRowAlgebra
