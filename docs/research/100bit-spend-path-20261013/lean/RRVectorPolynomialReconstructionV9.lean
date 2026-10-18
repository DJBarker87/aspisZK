import RRVectorNormalizedCompleteV3

open Polynomial
noncomputable section
namespace RRVectorPolynomialReconstruction
variable {K : Type*} [Field K]
open RRActualBivariateTaylorBridge RRVectorNormalizedComplete
open RRVectorRowPolynomialBridge RRVectorNormalizedRows RRRootDescent

/-- Embed an ordinary K-polynomial as a bivariate polynomial constant in the
inner coefficient variable. -/
theorem coeff_liftCoeffPolynomial (p : K[X]) (j : Nat) :
    (liftCoeffPolynomial p).coeff j = C (p.coeff j) := by
  simp [liftCoeffPolynomial, Polynomial.coeff_map]

/-- Reconstruct a bivariate polynomial from its first `N` inner-X coefficient
slices. -/
def sliceExpansion (q : Bivariate K) (N : Nat) : Bivariate K :=
  ∑ n ∈ Finset.range N,
    C ((X : K[X]) ^ n) * liftCoeffPolynomial (xCoeffSlice q n)

theorem sliceExpansion_eq_of_tail (q : Bivariate K) (N : Nat)
    (hN : 0 < N)
    (hzero : ∀ n, N ≤ n → xCoeffSlice q n = 0) :
    sliceExpansion q N = q := by
  have hdeg (j : Nat) : (q.coeff j).natDegree < N := by
    have hcoeff : ∀ n, N ≤ n → (q.coeff j).coeff n = 0 := by
      intro n hn
      have hslice : (xCoeffSlice q n).coeff j = 0 := by
        simpa using congrArg (fun p : K[X] => p.coeff j) (hzero n hn)
      simpa only [xCoeffSlice_coeff] using hslice
    have hle : (q.coeff j).natDegree ≤ N - 1 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
        intro n hn
        exact hcoeff n (by omega))
    omega
  ext j n
  rw [sliceExpansion, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul,
    coeff_liftCoeffPolynomial, xCoeffSlice_coeff]
  have hpoly :
      (∑ n ∈ Finset.range N,
          (X : K[X]) ^ n * C ((q.coeff j).coeff n)) = q.coeff j := by
    calc
      (∑ n ∈ Finset.range N,
          (X : K[X]) ^ n * C ((q.coeff j).coeff n)) =
        ∑ n ∈ Finset.range N, C ((q.coeff j).coeff n) * X ^ n := by
          apply Finset.sum_congr rfl
          intro n hn
          ring
      _ = q.coeff j :=
        (Polynomial.as_sum_range_C_mul_X_pow' (q.coeff j) (hdeg j)).symm
  exact congrArg (fun p : K[X] => p.coeff n) hpoly

/-- The exact normalized polynomial is reconstructed from the executable
`drop v` state, using the finite tail-zero theorem. -/
theorem normalized_model_reconstructs_child
    (gs : List (List K)) (a : K) (M ell v : Nat)
    (hdegree : ∀ i ≤ M, (inputPolynomial gs i).natDegree ≤ ell)
    (hlower : ∀ j t, t < v →
      (((actualParent gs M).comp (affine a)).coeff j).coeff t = 0)
    (hv : v ≤ M+ell) :
    sliceExpansion (actualChild gs a M v) (M+ell+1-v) = actualChild gs a M v := by
  apply sliceExpansion_eq_of_tail _ _ (by omega)
  intro n hn
  exact normalized_child_slice_zero_above_bound gs a M ell v n hdegree
    (by simpa [actualParent] using hlower) (by omega)

#print axioms sliceExpansion_eq_of_tail
#print axioms normalized_model_reconstructs_child
end RRVectorPolynomialReconstruction
