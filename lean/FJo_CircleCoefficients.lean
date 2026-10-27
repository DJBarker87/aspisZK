import FoldRuntimeAlgebra
import R1FirstFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_CircleCoefficients
open AspisV5ComponentCConcreteFoldLinearity AspisV5FriConcreteEncoderCommutation
open AspisV7ExactOneFoldDomains AspisV5FriDegreeThreeCorrelatedAgreement
/-- Isolate the field identity before instantiating the stored circle geometry;
no concrete domain points are reduced here. -/
theorem value {K : Type} [Field K] (alpha x y : K) (v : Fin 4 → K)
    (two : (2 : K)≠0) (hx : x≠0) (hy : y≠0) :
    FoldRuntimeAlgebra.circle alpha x y v=
      coefficientFoldValue alpha (radix4Decode (2*y)⁻¹ (-(2*y)⁻¹) (2*x)⁻¹ v) := by
  rw [FoldRuntimeAlgebra.circle_eq_model alpha x y v two hx hy]
  have h0 : 2*y*(2*y)⁻¹=1 := mul_inv_cancel₀ (mul_ne_zero two hy)
  have h1 : 2*(-y)*(-(2*y)⁻¹)=1 := by simpa only [mul_neg,neg_mul,neg_neg] using h0
  have h2 : 2*x*(2*x)⁻¹=1 := mul_inv_cancel₀ (mul_ne_zero two hx)
  have h := lineFoldValue_eq_coefficientFoldValue_decode alpha y (-y) x
    (2*y)⁻¹ (-(2*y)⁻¹) (2*x)⁻¹ h0 h1 h2
  simpa only [mul_neg,inv_neg] using h v
#print axioms value
end AspisR1.FJo_CircleCoefficients
end
