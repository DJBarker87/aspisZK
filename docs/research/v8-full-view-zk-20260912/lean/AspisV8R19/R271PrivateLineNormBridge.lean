import AspisV8R19.R270PrivateCoefficientExecution
import AspisV8R19.R243LineNormBridge

/-! The private coefficient evaluator at the already-proved source line
coordinate. Explicit unit-circle premise; no selected pointer/vector or
whole try_norm/callback correspondence is asserted. -/
set_option autoImplicit false
namespace AspisV8R19.R271PrivateLineNormBridge
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisR264PrivateCoefficientRaw.circle_norm.joined_inverse.line_norm.r110_norm (Coeff110)
open R250PrivateBaseExecution (encodeC)
open ComplexBaseExecution (encodeBase)
open R240HalfExecution (mapBase)
noncomputable section

theorem private_line_four (a b c : QM31Exact) (x y : M31Exact) :
    Coeff110.four (R270PrivateCoefficientExecution.coefficients a b c)
      (encodeBase x) (encodeBase y) (encodeBase (2*x^2-1)) =
        .ok (Array.make 4#usize [
          encodeC ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).1),
          encodeC ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.1),
          encodeC ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.2.1),
          encodeC ((R218CircleNormAlgebra.four a b c (mapBase x) (mapBase y)).2.2.2)]) := by
  rw [R270PrivateCoefficientExecution.coeff_four_exact,
    R243LineNormBridge.mapBase_line,R225LineNormAlgebra.lineFour_eq]

theorem mapped_circle (x y : M31Exact) (hcircle : x^2+y^2=1) :
    (mapBase x)^2+(mapBase y)^2=1 := by
  have hr1 : (1 : CM31Exact).re = (1 : M31Exact) := rfl
  have hi1 : (1 : CM31Exact).im = 0 := rfl
  apply QuadraticAlgebra.ext
  · simpa [mapBase,pow_two,QuadraticAlgebra.re_mul,hr1] using hcircle
  · simp [mapBase,pow_two,QuadraticAlgebra.im_mul,hi1]

theorem private_line_norms (a b c : QM31Exact) (x y : M31Exact)
    (hcircle : x^2+y^2=1) :
    Coeff110.four (R270PrivateCoefficientExecution.coefficients a b c)
      (encodeBase x) (encodeBase y) (encodeBase (2*x^2-1)) =
        .ok (Array.make 4#usize [
          encodeC (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (mapBase x) (mapBase y))),
          encodeC (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (mapBase x) (-mapBase y))),
          encodeC (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (-mapBase x) (-mapBase y))),
          encodeC (NormInverse.quarticNorm (R218CircleNormAlgebra.affine a b c (-mapBase x) (mapBase y)))]) := by
  rw [private_line_four,
    R218CircleNormAlgebra.four_exact a b c (mapBase x) (mapBase y) (mapped_circle x y hcircle)]

#print axioms private_line_four
#print axioms mapped_circle
#print axioms private_line_norms
end
end AspisV8R19.R271PrivateLineNormBridge
