import RRVectorNormalizedStateV4
import RRSubstitutionTailBound

open Polynomial
noncomputable section
namespace RRVectorNormalizedComplete
variable {K : Type*} [Field K]
open RRVectorNormalizedRows RRVectorNormalizedState RRRootDescent RRVectorRowPolynomialBridge
open RRActualBivariateTaylorBridge

def boundedState (gs : List (List K)) (a : K) (M ell v : Nat) : List (K[X]) :=
  normalizedVectorRows gs a M (M+ell) v

def normalizedModelRow (gs : List (List K)) (a : K) (M v k : Nat) : K[X] :=
  xCoeffSlice (actualChild gs a M v) k

/-- Readback for every coefficient row: the bounded executable state gives the
actual normalized-child rows inside its range, and every omitted row is zero. -/
theorem all_index_readback
    (gs : List (List K)) (a : K) (M ell v : Nat)
    (hdegree : ∀ i ≤ M, (inputPolynomial gs i).natDegree ≤ ell)
    (hlower : ∀ j t, t < v →
      (((actualParent gs M).comp (affine a)).coeff j).coeff t = 0)
    (hv : v ≤ M+ell) :
    ∀ k, (((boundedState gs a M ell v)[k]?) =
        if k < M+ell+1-v then some (normalizedModelRow gs a M v k) else none) ∧
      (M+ell+1-v ≤ k → normalizedModelRow gs a M v k = 0) := by
  intro k
  by_cases hk : k < M+ell+1-v
  · have hbound : v+k ≤ M+ell := by omega
    have hread := normalized_row_readback gs a M (M+ell) v k hlower hbound
    have hget : (boundedState gs a M ell v)[k]? =
        some (normalizedModelRow gs a M v k) := by
      simpa [boundedState, normalizedVectorRows, normalizedModelRow] using hread
    constructor
    · simp [hk, hget]
    · intro hfalse
      omega
  · have hlen : (boundedState gs a M ell v).length = M+ell+1-v := by
      simp [boundedState, normalized_state_length, hv]
    have hnone : (boundedState gs a M ell v)[k]? = none := by
      apply List.getElem?_eq_none
      rw [hlen]
      omega
    have htailIndex : M+ell < v+k := by omega
    have htail := normalized_child_slice_zero_above_bound
      gs a M ell v k hdegree (by simpa [actualParent] using hlower) htailIndex
    constructor
    · simp [hk, hnone]
    · intro _
      simpa [normalizedModelRow, actualChild, actualParent] using htail

#print axioms all_index_readback
end RRVectorNormalizedComplete
