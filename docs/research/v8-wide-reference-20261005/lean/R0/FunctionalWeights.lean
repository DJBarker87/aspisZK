import R0.LinearDual

set_option autoImplicit false
namespace AspisR0.FunctionalWeights
open scoped BigOperators
open AspisR0.LinearDual
noncomputable section
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
def row (f : (ι → K) →ₗ[K] K) : ι → K := fun i => f (Pi.single i 1)
theorem row_pairing (f : (ι → K) →ₗ[K] K) (q : ι → K) : dot (row f) q = f q := by
  have basis : q = ∑ i, q i • Pi.single i (1 : K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  conv_rhs => rw [basis]
  simp only [map_sum, map_smul, smul_eq_mul, row, dot]
  apply Finset.sum_congr rfl
  intro i _
  ring
#print axioms row_pairing
end
end AspisR0.FunctionalWeights
