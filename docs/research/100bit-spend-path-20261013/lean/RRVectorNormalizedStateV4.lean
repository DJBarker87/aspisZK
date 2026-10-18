import RRVectorNormalizedRowsV12

open Polynomial
noncomputable section
namespace RRVectorNormalizedState
variable {K : Type*} [Field K]
open RRVectorNormalizedRows RRRootDescent RRActualBivariateTaylorBridge

/-- Polynomial-model rows corresponding to a bounded list state. -/
def normalizedModelRows (gs : List (List K)) (a : K) (M B v : Nat) :
    List (K[X]) :=
  List.ofFn fun k : Fin (B+1-v) => xCoeffSlice (actualChild gs a M v) k.val

def normalizedVectorRows (gs : List (List K)) (a : K) (M B v : Nat) :
    List (K[X]) := (polynomialRows gs a M B).drop v

theorem normalized_state_length (gs : List (List K)) (a : K) (M B v : Nat)
    (hv : v ≤ B) :
    (normalizedVectorRows gs a M B v).length = (B+1-v) := by
  simp [normalizedVectorRows, polynomialRows_length]

theorem normalized_state_eq_model
    (gs : List (List K)) (a : K) (M B v : Nat)
    (hlower : ∀ j t, t < v →
      (((actualParent gs M).comp (affine a)).coeff j).coeff t = 0)
    (hv : v ≤ B) :
    normalizedVectorRows gs a M B v = normalizedModelRows gs a M B v := by
  apply List.ext_getElem?'
  intro k hk
  have hlen : (normalizedVectorRows gs a M B v).length = B+1-v :=
    normalized_state_length gs a M B v hv
  have hk' : k < B+1-v := by simpa [hlen, normalizedModelRows] using hk
  have hbound : v+k ≤ B := by omega
  have hread := normalized_row_readback gs a M B v k hlower hbound
  rw [normalizedVectorRows]
  rw [hread]
  simp [normalizedModelRows, hk']

#print axioms normalized_state_eq_model
end RRVectorNormalizedState
