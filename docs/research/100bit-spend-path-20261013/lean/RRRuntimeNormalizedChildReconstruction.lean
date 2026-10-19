import RRVectorNormalizedCompleteV3
import RRVectorPolynomialReconstructionV9

open Polynomial
noncomputable section
namespace AspisR1.RRRuntimeNormalizedChildReconstruction

variable {K : Type} [Field K]

/-- Concrete runtime normalization: the list of dense coefficient rows after
`drop v`. This stays in the executable `List (List K)` representation. -/
def runtimeRows (gs : List (List K)) (a : K) (M ell v : Nat) : List (List K) :=
  (RRVectorNormalizedRows.rowsThrough gs a M (M + ell)).drop v

/-- Polynomialize each stored runtime row, without changing its row order. -/
def runtimePolynomialRows (gs : List (List K)) (a : K) (M ell v : Nat) : List (K[X]) :=
  (runtimeRows gs a M ell v).map RRDenseCoeffVector.toPolynomial

theorem runtimePolynomialRows_eq_boundedState
    (gs : List (List K)) (a : K) (M ell v : Nat) :
    runtimePolynomialRows gs a M ell v =
      RRVectorNormalizedComplete.boundedState gs a M ell v := by
  simp [runtimePolynomialRows, runtimeRows,
    RRVectorNormalizedComplete.boundedState,
    RRVectorNormalizedState.normalizedVectorRows,
    RRVectorNormalizedRows.polynomialRows, List.map_drop]

theorem runtimePolynomialRows_eq_childModel
    (gs : List (List K)) (a : K) (M ell v : Nat)
    (hlower : ∀ j t, t < v →
      (((RRVectorNormalizedRows.actualParent gs M).comp
        (RRRootDescent.affine a)).coeff j).coeff t = 0)
    (hv : v ≤ M + ell) :
    runtimePolynomialRows gs a M ell v =
      RRVectorNormalizedState.normalizedModelRows gs a M (M + ell) v := by
  rw [runtimePolynomialRows_eq_boundedState]
  exact RRVectorNormalizedState.normalized_state_eq_model
    gs a M (M + ell) v hlower hv

theorem runtimePolynomialRows_all_index_readback
    (gs : List (List K)) (a : K) (M ell v : Nat)
    (hdegree : ∀ i ≤ M, (RRVectorRowPolynomialBridge.inputPolynomial gs i).natDegree ≤ ell)
    (hlower : ∀ j t, t < v →
      (((RRVectorNormalizedRows.actualParent gs M).comp
        (RRRootDescent.affine a)).coeff j).coeff t = 0)
    (hv : v ≤ M + ell) :
    ∀ k, (runtimePolynomialRows gs a M ell v)[k]? =
      if k < M + ell + 1 - v then
        some (RRVectorNormalizedComplete.normalizedModelRow gs a M v k)
      else none := by
  intro k
  rw [runtimePolynomialRows_eq_boundedState]
  exact (RRVectorNormalizedComplete.all_index_readback
    gs a M ell v hdegree hlower hv k).1

theorem runtimeState_reconstructs_actualChild
    (gs : List (List K)) (a : K) (M ell v : Nat)
    (hdegree : ∀ i ≤ M, (RRVectorRowPolynomialBridge.inputPolynomial gs i).natDegree ≤ ell)
    (hlower : ∀ j t, t < v →
      (((RRVectorNormalizedRows.actualParent gs M).comp
        (RRRootDescent.affine a)).coeff j).coeff t = 0)
    (hv : v ≤ M + ell) :
    runtimePolynomialRows gs a M ell v =
        RRVectorNormalizedState.normalizedModelRows gs a M (M + ell) v ∧
      (∀ k, (runtimePolynomialRows gs a M ell v)[k]? =
        if k < M + ell + 1 - v then
          some (RRVectorNormalizedComplete.normalizedModelRow gs a M v k)
        else none) ∧
      RRVectorPolynomialReconstruction.sliceExpansion
          (RRVectorNormalizedRows.actualChild gs a M v) (M + ell + 1 - v) =
        RRVectorNormalizedRows.actualChild gs a M v := by
  refine ⟨runtimePolynomialRows_eq_childModel gs a M ell v hlower hv, ?_, ?_⟩
  · intro k
    exact runtimePolynomialRows_all_index_readback gs a M ell v hdegree hlower hv k
  · exact RRVectorPolynomialReconstruction.normalized_model_reconstructs_child
      gs a M ell v hdegree hlower hv

#print axioms runtimeState_reconstructs_actualChild
end AspisR1.RRRuntimeNormalizedChildReconstruction
