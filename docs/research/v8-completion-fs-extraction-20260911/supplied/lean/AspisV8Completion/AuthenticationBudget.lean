/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.AuthenticationBudget
noncomputable section

/-- Union-count ceiling. It is deliberately parameterised by a real fresh
query budget, not by the number of honest-verifier hash calls alone. -/
def collisionBound (Q bits : Nat) : ℚ :=
  (Q : ℚ)*(Q-1:Nat)/(2*(2:ℚ)^bits)

def targetBound (Q targets bits : Nat) : ℚ :=
  (Q:ℚ)*targets/(2:ℚ)^bits

/-- Pair counting by induction: i prior fresh answers at fresh query i.
The separate adaptive hazard proof supplies the probabilistic step. -/
theorem prior_pairs (Q : Nat) :
    2 * (∑ i ∈ Finset.range Q, i) = Q*(Q-1) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_range_succ]
    cases Q with
    | zero => norm_num at *
    | succ k => simp only [Nat.succ_sub_one] at *; nlinarith

/-- C1 and C2 target families need not be independent; charge their union. -/
theorem two_target_union (Q m1 m2 bits : Nat) :
    targetBound Q m1 bits + targetBound Q m2 bits = targetBound Q (m1+m2) bits := by
  unfold targetBound
  push_cast
  ring

/-- A resource-dependent arithmetic criterion, not an unconditional hash theorem. -/
theorem total_auth_le (collision c1 c2 cap : ℚ)
    (h : collision+c1+c2 ≤ cap) : collision+(c1+c2) ≤ cap := by linarith

#print axioms prior_pairs
#print axioms two_target_union
end
end AspisV8Completion.AuthenticationBudget
