import RRConcreteChildModel
import RRConcreteState

open Polynomial
noncomputable section
namespace AspisR1.RRConcreteRawStateValidity

open RRVectorNormalizedRows RRVectorNormalizedState RRVectorNormalizedComplete
open RRVectorPolynomialReconstruction RRVectorRowPolynomialBridge
open RRRuntimeNormalizedChildReconstruction RRRootDescent
open RRActualBivariateTaylorBridge
open AspisR1.RRConcreteState

variable {K : Type} [Field K] [BEq K] [LawfulBEq K]

/-- Every runtime row of the dropped normalization state is the corresponding
coefficient slice of the mathematical child. -/
theorem runtime_input_row_eq_slice
    (gs : List (List K)) (a : K) (M ell v i : Nat)
    (hdegree : ∀ j ≤ M, (inputPolynomial gs j).natDegree ≤ ell)
    (hlower : ∀ j t, t < v →
      (((actualParent gs M).comp (affine a)).coeff j).coeff t = 0)
    (hv : v ≤ M + ell) (hi : i < M + ell + 1 - v) :
    inputPolynomial (runtimeRows gs a M ell v) i =
      xCoeffSlice (actualChild gs a M v) i := by
  have hread := runtimePolynomialRows_all_index_readback
    gs a M ell v hdegree hlower hv i
  simp only [if_pos hi] at hread
  change (runtimePolynomialRows gs a M ell v)[i]? =
    some (normalizedModelRow gs a M v i) at hread
  rw [runtimePolynomialRows, List.getElem?_map] at hread
  cases hsource : (runtimeRows gs a M ell v)[i]? with
  | none => simp [hsource] at hread
  | some row =>
    simp [hsource] at hread
    have hpoly : RRDenseCoeffVector.toPolynomial row =
        normalizedModelRow gs a M v i := hread
    simpa [inputPolynomial, vectorAt, hsource, normalizedModelRow] using hpoly

/-- The actual executable normalized child is a valid recursive RawState.
The first-slice nonzero fact is supplied by the finite scanner; the uniform
degree part follows for every coefficient address, not only returned roots. -/
theorem runtime_child_state_valid
    (gs : List (List K)) (a : K) (M ell v : Nat)
    (hdegree : ∀ j ≤ M, (inputPolynomial gs j).natDegree ≤ ell)
    (hlower : ∀ j t, t < v →
      (((actualParent gs M).comp (affine a)).coeff j).coeff t = 0)
    (hv : v ≤ M + ell)
    (hfirst : xCoeffSlice (actualChild gs a M v) 0 ≠ 0) :
    Valid ell ⟨runtimeRows gs a M ell v, M + ell - v⟩ := by
  change inputPolynomial (runtimeRows gs a M ell v) 0 ≠ 0 ∧
    ∀ i ≤ M + ell - v,
      (inputPolynomial (runtimeRows gs a M ell v) i).natDegree ≤ ell
  constructor
  · rw [runtime_input_row_eq_slice gs a M ell v 0 hdegree hlower hv (by omega)]
    exact hfirst
  · intro i hi
    rw [runtime_input_row_eq_slice gs a M ell v i hdegree hlower hv (by omega)]
    exact normalized_child_slice_degree_le gs a M ell v i hdegree (by
      simpa [actualParent] using hlower)

#print axioms runtime_input_row_eq_slice
#print axioms runtime_child_state_valid
end AspisR1.RRConcreteRawStateValidity
