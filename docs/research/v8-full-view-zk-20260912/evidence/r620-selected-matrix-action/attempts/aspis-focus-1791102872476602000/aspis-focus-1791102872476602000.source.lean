import AspisV8R19.R619MatrixArithmeticBridge
import AspisV8R19.ProductCorrectness
set_option autoImplicit false
namespace AspisV8R19.R620MatrixAction
open AspisV8R15.ExactTowerBase (M31Exact QM31Exact)

theorem qm31_product_coordinates (a b c d e f g h : M31Exact) :
    (⟨⟨a,b⟩,⟨c,d⟩⟩ : QM31Exact) * ⟨⟨e,f⟩,⟨g,h⟩⟩ =
      ⟨⟨a*e-b*f+(2*c-d)*g-(c+2*d)*h,
         b*e+a*f+(c+2*d)*g+(2*c-d)*h⟩,
       ⟨c*e-d*f+a*g-b*h,
         d*e+c*f+b*g+a*h⟩⟩ := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      AspisV8R15.ExactTowerBase.qm31R_re,
      AspisV8R15.ExactTowerBase.qm31R_im,
      QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero] <;> ring

#print axioms qm31_product_coordinates
end AspisV8R19.R620MatrixAction
