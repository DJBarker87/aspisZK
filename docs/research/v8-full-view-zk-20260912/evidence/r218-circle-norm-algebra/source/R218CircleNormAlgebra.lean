import AspisV8R19.NormInverse

/-! Algebraic predecessor for the selected circle/line norm optimization.
No word-level coefficient-loop or vector execution identity is asserted. -/
set_option autoImplicit false
namespace AspisV8R19.R218CircleNormAlgebra
open AspisV8R15.ExactTowerBase
noncomputable section

def polar (v w : QM31Exact) : CM31Exact :=
  (v.re*w.re-qm31R*(v.im*w.im))*2

def affine (a b c : QM31Exact) (x y : CM31Exact) : QM31Exact :=
  a+b*(algebraMap CM31Exact QM31Exact x)+c*(algebraMap CM31Exact QM31Exact y)

theorem norm_affine (a b c : QM31Exact) (x y : CM31Exact) :
    NormInverse.quarticNorm (affine a b c x y) =
      NormInverse.quarticNorm a+NormInverse.quarticNorm b*x^2+
      NormInverse.quarticNorm c*y^2+polar a b*x+polar a c*y+polar b c*(x*y) := by
  simp [NormInverse.quarticNorm,affine,polar,
    QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
  ring

/-- The exact ordered four sign fibres used by the selected source. -/
def four (a b c : QM31Exact) (x y : CM31Exact) :
    CM31Exact × CM31Exact × CM31Exact × CM31Exact :=
  let even := (NormInverse.quarticNorm a+NormInverse.quarticNorm c)+
    (NormInverse.quarticNorm b-NormInverse.quarticNorm c)*x^2
  let odd_x := polar a b*x
  let odd_y := polar a c*y
  let cross := polar b c*(x*y)
  let positive := even+odd_x
  let negative := even-odd_x
  let plus := odd_y+cross
  let minus := odd_y-cross
  (positive+plus,positive-plus,negative-minus,negative+minus)

theorem four_exact (a b c : QM31Exact) (x y : CM31Exact)
    (hcircle : x^2+y^2=1) :
    four a b c x y =
      (NormInverse.quarticNorm (affine a b c x y),
       NormInverse.quarticNorm (affine a b c x (-y)),
       NormInverse.quarticNorm (affine a b c (-x) (-y)),
       NormInverse.quarticNorm (affine a b c (-x) y)) := by
  have hy : y^2=1-x^2 := by linear_combination hcircle
  simp only [four,norm_affine,neg_sq,hy]
  apply Prod.ext
  · ring
  · apply Prod.ext
    · ring
    · apply Prod.ext <;> ring

#print axioms norm_affine
#print axioms four_exact
end
end AspisV8R19.R218CircleNormAlgebra
