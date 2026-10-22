import R1Z.ProverCommitMaskPolynomial50
/-! Exact finite reconstruction of the selected-mask polynomial. Native
coefficient storage must still be identified with these mathematical cells. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitMaskCoefficients50
open Polynomial
open scoped BigOperators
variable {K : Type} [Field K] {F : Subfield K}

theorem outside (B : R0P.PackBasis F) (c1 : Fin 16 → K) (mo : Fin 10 → K) (k : Nat) (hk : 27≤k) :
    (ProverCommitMaskPolynomial50.polynomial B c1 mo).coeff k=0 := by
  have h1 (c : Fin 16) : (R0P.Mask.factorExponent c).val≠k := by
    have := (R0P.Mask.factorExponent c).isLt
    omega
  have h2 (c : Fin 10) : (R0P.Mask.maskOnlyFactorExponent c).val≠k := by
    have := (R0P.Mask.maskOnlyFactorExponent c).isLt
    omega
  simp only [ProverCommitMaskPolynomial50.polynomial,Polynomial.coeff_add,
    Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,h1,h2,if_false,Finset.sum_const_zero,add_zero]

theorem reconstruct (B : R0P.PackBasis F) (c1 : Fin 16 → K) (mo : Fin 10 → K) :
    ProverCommitInterpolationPoly48.poly 27 (fun k => (ProverCommitMaskPolynomial50.polynomial B c1 mo).coeff k)=
      ProverCommitMaskPolynomial50.polynomial B c1 mo := by
  ext k
  rw [ProverCommitInterpolationPoly48.coeff]
  by_cases hk : k<27
  · rw [if_pos hk]
  · rw [if_neg hk,outside B c1 mo k (by omega)]

theorem eval_mask (B : R0P.PackBasis F) (c1 : Fin 16 → K) (mo : Fin 10 → K) (g : K) (a : Fin 10 → K) :
    (ProverCommitInterpolationPoly48.poly 27
      (fun k => (ProverCommitMaskPolynomial50.polynomial B c1 mo).coeff k)).eval (R0P.Mask.maskLinear 0 a)+
      (1+R0P.Mask.maskLinear 16 a^26)*g=R0P.Mask.maskValue B c1 mo g a := by
  rw [reconstruct,ProverCommitMaskPolynomial50.eval_mask]

#print axioms outside
#print axioms reconstruct
#print axioms eval_mask
end R1Z.ProverCommitMaskCoefficients50
