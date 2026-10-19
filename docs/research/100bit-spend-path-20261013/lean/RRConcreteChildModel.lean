import RRRuntimeNormalizedChildReconstruction

open Polynomial
noncomputable section
namespace AspisR1.RRConcreteChildModel

open RRVectorNormalizedRows RRVectorNormalizedState RRVectorNormalizedComplete
open RRVectorPolynomialReconstruction RRVectorRowPolynomialBridge
open RRRuntimeNormalizedChildReconstruction RRRootDescent

variable {K : Type} [Field K]

/-- The runtime child rows, interpreted as the actual bounded parent model,
are exactly the polynomial child produced by the normalized transition. -/
theorem runtime_parent_eq_actual_child
    (gs : List (List K)) (a : K) (M ell v : Nat)
    (hdegree : ∀ i ≤ M, (inputPolynomial gs i).natDegree ≤ ell)
    (hlower : ∀ j t, t < v →
      (((actualParent gs M).comp (affine a)).coeff j).coeff t = 0)
    (hv : v ≤ M + ell) :
    actualParent (runtimeRows gs a M ell v) (M + ell - v) =
      actualChild gs a M v := by
  let child := actualChild gs a M v
  let n := M + ell + 1 - v
  have hrow (i : Nat) (hi : i < n) :
      inputPolynomial (runtimeRows gs a M ell v) i =
        normalizedModelRow gs a M v i := by
    have hread := runtimePolynomialRows_all_index_readback
      gs a M ell v hdegree hlower hv i
    have hi : i < M + ell + 1 - v := by simpa [n] using hi
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
      simpa [inputPolynomial, vectorAt, hsource] using hpoly
  have hparent :
      parentFromSlices (inputPolynomial (runtimeRows gs a M ell v)) (n-1) =
        sliceExpansion child n := by
    unfold parentFromSlices sliceExpansion
    have hrange : n - 1 + 1 = n := by omega
    rw [hrange]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    rw [hrow i hin]
    dsimp [normalizedModelRow, child]
  have hn : n - 1 = M + ell - v := by dsimp [n]; omega
  calc
    actualParent (runtimeRows gs a M ell v) (M + ell - v) =
        parentFromSlices (inputPolynomial (runtimeRows gs a M ell v)) (n-1) := by
          simp [actualParent, hn]
    _ = sliceExpansion child n := hparent
    _ = child := by
          dsimp [child, n]
          exact normalized_model_reconstructs_child gs a M ell v
            hdegree hlower hv

#print axioms runtime_parent_eq_actual_child
end AspisR1.RRConcreteChildModel
