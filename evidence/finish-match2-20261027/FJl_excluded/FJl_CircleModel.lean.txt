import FJl_SlotLiteral
import FoldRuntimeAlgebra
import R1FirstFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_CircleModel
open AspisWide.InitialEncoder AspisWide.FinalEncoder
open AspisV5ComponentCConcreteFoldLinearity AspisV5FriConcreteEncoderCommutation
attribute [local irreducible] exactCircleX exactCircleY
abbrev E := AspisWideTower.WideExact
/-- The symbolic native circle expression is the original model first fold
on precisely the SAME four fibre coordinates. -/
theorem value (alpha : E) (f : AspisPool.AlgorithmicCircleDecoderV7.InitialWord E)
    (i : Fin 262144) :
    FoldRuntimeAlgebra.circle alpha (exactCircleX i) (exactCircleY i) (FirstFold.fibre f i)=
      FirstFold.foldWord alpha f i := by
  have nz := FirstFold.fibre_coordinates_nonzero (K := E) i
  rw [FoldRuntimeAlgebra.circle_eq_model alpha _ _ _ AspisWide.InitialEncoder.two_ne_zero nz.1 nz.2]
  have h0 : 2*exactCircleY i*(2*exactCircleY (K:=E) i)⁻¹=1 :=
    mul_inv_cancel₀ (mul_ne_zero AspisWide.InitialEncoder.two_ne_zero nz.2)
  have h1 : 2*(-exactCircleY i)*(-(2*exactCircleY (K:=E) i)⁻¹)=1 := by
    simpa only [mul_neg,neg_mul,neg_neg] using h0
  have h2 : 2*exactCircleX i*(2*exactCircleX (K:=E) i)⁻¹=1 :=
    mul_inv_cancel₀ (mul_ne_zero AspisWide.InitialEncoder.two_ne_zero nz.1)
  have source := lineFoldValue_eq_coefficientFoldValue_decode alpha
    (exactCircleY i) (-exactCircleY i) (exactCircleX i)
    (2*exactCircleY i)⁻¹ (-(2*exactCircleY i)⁻¹) (2*exactCircleX i)⁻¹ h0 h1 h2
  simpa only [FirstFold.foldWord,FirstFold.channels,FirstFold.fibreTransform,mul_neg,inv_neg] using
    source (FirstFold.fibre f i)
#print axioms value
end AspisR1.FJl_CircleModel
end
