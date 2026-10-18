import RRScannedNormalizedTransition

open Polynomial
noncomputable section
namespace RRRootDescent
variable {K : Type*} [Field K]
open RRActualBivariateTaylorBridge RRVectorRowPolynomialBridge

/-- Affine substitution raises the inner-X degree by at most the original
outer-Y degree. No omitted vector row can be nonzero beyond M+ell. -/
theorem fixed_parent_slice_zero_above_bound
    (gs : List (List K)) (a : K) (M ell n : Nat)
    (hdegree : ∀ i ≤ M, (inputPolynomial gs i).natDegree ≤ ell)
    (hn : M + ell < n) :
    xCoeffSlice (fixedParentSlice (inputPolynomial gs) a M) n = 0 := by
  ext j
  rw [parentCoefficient_eq_rowValue, coeff_zero]
  unfold rowValue
  by_cases hj : j ≤ n
  · rw [if_pos hj]
    by_cases hi : n - j ≤ M
    · rw [if_pos hi]
      have hjlarge : ell < j := by omega
      have hz : (Polynomial.taylor a (inputPolynomial gs (n-j))).coeff j = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Polynomial.natDegree_taylor]
        exact lt_of_le_of_lt (hdegree (n-j) hi) hjlarge
      simpa only [inputPolynomial, RRDenseCoeffVector.taylor_coeff_toPolynomial] using hz
    · rw [if_neg hi]
  · rw [if_neg hj]

/-- After normalization at v, the finite representation needs only rows
with v+k at most M+ell. Every omitted normalized row is zero. -/
theorem normalized_child_slice_zero_above_bound
    (gs : List (List K)) (a : K) (M ell v k : Nat)
    (hdegree : ∀ i ≤ M, (inputPolynomial gs i).natDegree ≤ ell)
    (hlower : ∀ j t, t < v →
      (((parentFromSlices (inputPolynomial gs) M).comp (affine a)).coeff j).coeff t = 0)
    (hk : M + ell < v + k) :
    xCoeffSlice
      (stripInnerPower ((parentFromSlices (inputPolynomial gs) M).comp (affine a)) v) k = 0 := by
  ext j
  rw [xCoeffSlice_coeff, stripInnerPower_coeff_readback _ v j k hlower, coeff_zero]
  have hz := congrArg (fun p : K[X] => p.coeff j)
    (fixed_parent_slice_zero_above_bound gs a M ell (v+k) hdegree hk)
  rw [xCoeffSlice_coeff, coeff_zero] at hz
  rw [parentFromSlices_comp]
  exact hz

#print axioms fixed_parent_slice_zero_above_bound
#print axioms normalized_child_slice_zero_above_bound
end RRRootDescent
