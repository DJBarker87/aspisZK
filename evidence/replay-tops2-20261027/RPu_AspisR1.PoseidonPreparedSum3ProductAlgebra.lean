import RPu_AspisR1.PoseidonPreparedKaratsubaAggregateAlgebra
import RPu_AspisR1.PoseidonPreparedRowSumAlgebra

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedSum3ProductAlgebra
open AspisV8R15.ExactTowerBase

abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev QMExact := AspisV8R15.ExactTowerBase.QM31Exact

private theorem qm_re_mul (x y : QMExact) :
    (x * y).re = x.re * y.re + qm31R * (x.im * y.im) := by
  calc
    (x * y).re = x.re * y.re + qm31R * x.im * y.im := QuadraticAlgebra.re_mul x y
    _ = x.re * y.re + qm31R * (x.im * y.im) := by ring

private theorem qm_im_mul (x y : QMExact) :
    (x * y).im = x.re * y.im + x.im * y.re + 0 * (x.im * y.im) := by
  simpa [QMExact] using (QuadraticAlgebra.im_mul x y)

theorem sum3_qm_products (x00 x01 x10 x11 x20 x21 y00 y01 y10 y11 y20 y21 : CMExact) :
    (⟨x00*y00 + x10*y10 + x20*y20 +
          qm31R * (x01*y01 + x11*y11 + x21*y21),
      (x00+x01)*(y00+y01) + (x10+x11)*(y10+y11) + (x20+x21)*(y20+y21) -
          (x00*y00 + x10*y10 + x20*y20) - (x01*y01 + x11*y11 + x21*y21)⟩ : QMExact) =
      (⟨x00,x01⟩ : QMExact) * ⟨y00,y01⟩ +
      (⟨x10,x11⟩ : QMExact) * ⟨y10,y11⟩ +
      (⟨x20,x21⟩ : QMExact) * ⟨y20,y21⟩ := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_add, qm_re_mul]
    ring
  · simp only [QuadraticAlgebra.im_add, qm_im_mul]
    ring

#print axioms sum3_qm_products
end AspisR1.PoseidonPreparedSum3ProductAlgebra
