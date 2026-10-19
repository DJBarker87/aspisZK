import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-! The transpose weights of a linear message map. -/
set_option autoImplicit false
namespace AspisR0.LinearDual
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

def dot (w q : ι → K) : K := ∑ i, w i * q i

def weights (L : (ι → K) →ₗ[K] (ι → K)) (w : ι → K) : ι → K :=
  fun i => dot w (L (Pi.single i 1))

theorem transpose_pairing (L : (ι → K) →ₗ[K] (ι → K)) (w q : ι → K) :
    dot w (L q) = dot (weights L w) q := by
  have basis : q = ∑ i, q i • Pi.single i (1 : K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  conv_lhs => rw [basis]
  simp only [map_sum, map_smul, dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, weights]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms transpose_pairing
end
end AspisR0.LinearDual
