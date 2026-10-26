import R1Z.ProverRwEntropyKernel64
set_option autoImplicit false
namespace R1Z.ProverRwEntropySum64
open scoped BigOperators

/-- Keep finite-carrier algebra abstract before specializing to 512-bit raw
seeds or their nonzero subtype. No concrete carrier enumeration is reduced. -/
theorem swap_weighted_sum {X Y : Type} [Fintype X] [Fintype Y]
    (weight : Y → ℚ) (term : X → Y → ℚ) :
    (∑ x : X, ∑ y : Y, weight y * term x y) =
      ∑ y : Y, weight y * ∑ x : X, term x y := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]

#print axioms swap_weighted_sum
end R1Z.ProverRwEntropySum64
