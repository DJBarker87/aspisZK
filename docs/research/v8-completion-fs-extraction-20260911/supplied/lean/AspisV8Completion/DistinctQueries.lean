/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.DistinctQueries

/-- Explicit rational recurrence; do not replace a source query sampler by
this law until rejection/duplicate handling and chronology are refined. -/
def allIn (N M : Nat) : Nat → ℚ
  | 0 => 1
  | q+1 => if q < M then allIn N M q * ((M-q:Nat):ℚ)/(N-q:Nat) else 0

theorem allIn_zero (N M : Nat) : allIn N M 0=1 := rfl

theorem over_subset_zero (N M q : Nat) (outside : M ≤ q) : allIn N M (q+1)=0 := by
  simp [allIn, Nat.not_lt.mpr outside]

/-- Ordered distinct samples can only reduce the all-in-subset probability
relative to the with-replacement factor, while positive denominators hold. -/
theorem conditional_fraction_le (N M i : ℚ)
    (hN : 0 < N) (hM : M ≤ N) (hi : 0 ≤ i) (inside : i < N) :
    (M-i)/(N-i) ≤ M/N := by
  apply (div_le_div_iff₀ (by linarith : 0 < N-i) hN).2
  nlinarith

#print axioms conditional_fraction_le
end AspisV8Completion.DistinctQueries
