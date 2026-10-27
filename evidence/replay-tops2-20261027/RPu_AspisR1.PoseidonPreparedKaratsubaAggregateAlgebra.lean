import RPu_AspisR1.PoseidonPreparedChannelRowProduct

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedKaratsubaAggregateAlgebra
open AspisV8R15.ExactTowerBase

abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev QMExact := AspisV8R15.ExactTowerBase.QM31Exact

private theorem qm_re_mul (x y : QMExact) :
    (x * y).re = x.re * y.re + AspisV8R15.ExactTowerBase.qm31R * (x.im * y.im) := by
  calc
    (x * y).re = x.re * y.re + AspisV8R15.ExactTowerBase.qm31R * x.im * y.im :=
      QuadraticAlgebra.re_mul x y
    _ = x.re * y.re + AspisV8R15.ExactTowerBase.qm31R * (x.im * y.im) := by ring

private theorem qm_im_mul (x y : QMExact) :
    (x * y).im = x.re * y.im + x.im * y.re + 0 * (x.im * y.im) := by
  simpa [QMExact] using (QuadraticAlgebra.im_mul x y)

/-- The converter's three-row expression is exactly the product in the outer
quadratic extension; the second component is the Karatsuba cross term. -/
theorem converter_eq_qm_mul (x0 x1 y0 y1 : CMExact) :
    (⟨x0 * y0 + (AspisV8R15.ExactTowerBase.qm31R * (x1 * y1)),
      (x0 + x1) * (y0 + y1) - x0 * y0 - x1 * y1⟩ : QMExact) =
      (⟨x0, x1⟩ : QMExact) * ⟨y0, y1⟩ := by
  apply QuadraticAlgebra.ext
  · rw [qm_re_mul]
  · rw [qm_im_mul]
    simp [AspisV8R15.ExactTowerBase.qm31R]
    ring

#print axioms converter_eq_qm_mul
end AspisR1.PoseidonPreparedKaratsubaAggregateAlgebra
