import AspisV8R19.R218CircleNormAlgebra

/-! Exact line-coordinate rewrite for selected four-fibre norm algebra.
The explicit 2*x^2-1 input is not a proof of source line provenance or half
execution. Those remain source obligations. -/
set_option autoImplicit false
namespace AspisV8R19.R225LineNormAlgebra
open AspisV8R15.ExactTowerBase
noncomputable section

theorem two_nonzero : (2 : CM31Exact) ≠ 0 := by
  have hm : (2 : M31Exact) ≠ 0 := by decide
  intro h
  exact hm (congrArg QuadraticAlgebra.re h)

theorem even_exact (a b x : CM31Exact) :
    (a+b/2)+(b/2)*(2*x^2-1) = a+b*x^2 := by
  field_simp [two_nonzero]
  ring

def lineFour (a b c : QM31Exact) (x y t : CM31Exact) :
    CM31Exact × CM31Exact × CM31Exact × CM31Exact :=
  let c0 := NormInverse.quarticNorm a+NormInverse.quarticNorm c
  let c1 := NormInverse.quarticNorm b-NormInverse.quarticNorm c
  let half := c1/2
  let even := (c0+half)+half*t
  let odd_x := R218CircleNormAlgebra.polar a b*x
  let odd_y := R218CircleNormAlgebra.polar a c*y
  let cross := R218CircleNormAlgebra.polar b c*(x*y)
  let positive := even+odd_x
  let negative := even-odd_x
  let plus := odd_y+cross
  let minus := odd_y-cross
  (positive+plus,positive-plus,negative-minus,negative+minus)

theorem lineFour_eq (a b c : QM31Exact) (x y : CM31Exact) :
    lineFour a b c x y (2*x^2-1) = R218CircleNormAlgebra.four a b c x y := by
  simp only [lineFour,R218CircleNormAlgebra.four,even_exact]

theorem lineFour_exact (a b c : QM31Exact) (x y : CM31Exact)
    (hcircle : x^2+y^2=1) :
    lineFour a b c x y (2*x^2-1) =
      (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c x y),
       NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c x (-y)),
       NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (-x) (-y)),
       NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (-x) y)) := by
  rw [lineFour_eq,R218CircleNormAlgebra.four_exact a b c x y hcircle]

#print axioms two_nonzero
#print axioms even_exact
#print axioms lineFour_eq
#print axioms lineFour_exact
end
end AspisV8R19.R225LineNormAlgebra
