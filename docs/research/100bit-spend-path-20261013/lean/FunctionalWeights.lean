import R1JointFunctionalBinding
import R1RoundPairing

/-! Exact coefficient weights for a linear functional on a finite vector.
This does not identify any Rust weight constructor with these weights. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.FunctionalWeights

open scoped BigOperators
variable {K : Type} [Field K]

def weightedMap {n : Nat} (F : Fin 6 → (Fin n → K) →ₗ[K] K)
    (F0 : (Fin n → K) →ₗ[K] K) (kappa : K) : (Fin n → K) →ₗ[K] K :=
  F0 + ∑ j : Fin 6, kappa ^ (j.val + 1) • F j

def weights {n : Nat} (F : Fin 6 → (Fin n → K) →ₗ[K] K)
    (F0 : (Fin n → K) →ₗ[K] K) (kappa : K) : Fin n → K :=
  fun i => weightedMap F F0 kappa (Pi.single i 1)

theorem vector_eq_sum_single {n : Nat} (q : Fin n → K) :
    q = ∑ i : Fin n, q i • Pi.single i (1 : K) := by
  funext d
  simp [Pi.single_apply]

theorem linear_eq_dot {n : Nat} (L : (Fin n → K) →ₗ[K] K)
    (q : Fin n → K) :
    L q = AspisR1.RoundPairing.dot q (fun i => L (Pi.single i 1)) := by
  have h := congrArg L (vector_eq_sum_single q)
  simpa only [map_sum, map_smul, smul_eq_mul, AspisR1.RoundPairing.dot] using h

theorem dot_weights {n : Nat} (F : Fin 6 → (Fin n → K) →ₗ[K] K)
    (F0 : (Fin n → K) →ₗ[K] K) (kappa : K) (q : Fin n → K) :
    AspisR1.RoundPairing.dot q (weights F F0 kappa) =
      F0 q + ∑ j : Fin 6, kappa ^ (j.val + 1) * F j q := by
  unfold weights
  rw [← linear_eq_dot (weightedMap F F0 kappa) q]
  simp [weightedMap]

#print axioms vector_eq_sum_single
#print axioms linear_eq_dot
#print axioms dot_weights
end AspisR1.FunctionalWeights
end
