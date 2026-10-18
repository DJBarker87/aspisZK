import RRSubstitutionTailBound

open Polynomial
noncomputable section
namespace RRRootDescent
variable {K : Type*} [Field K]
open RRActualBivariateTaylorBridge RRVectorRowPolynomialBridge

/-- Substitution does not increase the outer-Y degree, for any inner row. -/
theorem fixed_parent_slice_degree_le
    (gs : List (List K)) (a : K) (M ell n : Nat)
    (hdegree : ∀ i ≤ M, (inputPolynomial gs i).natDegree ≤ ell) :
    (xCoeffSlice (fixedParentSlice (inputPolynomial gs) a M) n).natDegree ≤ ell := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [parentCoefficient_eq_rowValue]
  unfold rowValue
  by_cases hjn : j ≤ n
  · rw [if_pos hjn]
    by_cases hi : n-j ≤ M
    · rw [if_pos hi]
      have hz : (Polynomial.taylor a (inputPolynomial gs (n-j))).coeff j = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Polynomial.natDegree_taylor]
        exact lt_of_le_of_lt (hdegree (n-j) hi) hj
      simpa only [inputPolynomial, RRDenseCoeffVector.taylor_coeff_toPolynomial] using hz
    · rw [if_neg hi]
  · rw [if_neg hjn]

/-- The uniform outer-Y degree bound is preserved after stripping inner-X
coefficients. It therefore remains available at every recursive decoder step. -/
theorem normalized_child_slice_degree_le
    (gs : List (List K)) (a : K) (M ell v k : Nat)
    (hdegree : ∀ i ≤ M, (inputPolynomial gs i).natDegree ≤ ell)
    (hlower : ∀ j t, t < v →
      (((parentFromSlices (inputPolynomial gs) M).comp (affine a)).coeff j).coeff t = 0) :
    (xCoeffSlice
      (stripInnerPower ((parentFromSlices (inputPolynomial gs) M).comp (affine a)) v) k).natDegree ≤ ell := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [xCoeffSlice_coeff, stripInnerPower_coeff_readback _ v j k hlower,
    parentFromSlices_comp]
  have h := Polynomial.natDegree_le_iff_coeff_eq_zero.mp
    (fixed_parent_slice_degree_le gs a M ell (v+k) hdegree) j hj
  simpa only [xCoeffSlice_coeff] using h

#print axioms fixed_parent_slice_degree_le
#print axioms normalized_child_slice_degree_le
end RRRootDescent
