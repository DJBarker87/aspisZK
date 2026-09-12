/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.CommonSupport
noncomputable section
variable {I C V : Type*} [DecidableEq I]

/-- One support set controls every column jointly: no multiplication by the
number of columns. This is a deterministic fact; sampling remains separate. -/
def JointGood (columns : C → I → V) (expected : C → I → V) (S : Finset I) : Prop :=
  ∀ i, i ∉ S → ∀ column, columns column i = expected column i

theorem joint_failure_in_support (columns expected : C → I → V) (S : Finset I)
    (good : JointGood columns expected S) (i : I)
    (failure : ∃ column, columns column i ≠ expected column i) : i ∈ S := by
  by_contra outside
  obtain ⟨c,hc⟩ := failure
  exact hc (good i outside c)

/-- Union of two discrepancy supports. Useful when transporting quotient,
original and helper agreements without silently losing chord-pole positions. -/
theorem equality_outside_union {a b c : I → V} {S T : Finset I}
    (ab : ∀ i, i ∉ S → a i=b i) (bc : ∀ i, i ∉ T → b i=c i) :
    ∀ i, i ∉ S∪T → a i=c i := by
  intro i outside
  have hs : i ∉ S := fun h => outside (Finset.mem_union_left T h)
  have ht : i ∉ T := fun h => outside (Finset.mem_union_right S h)
  exact (ab i hs).trans (bc i ht)

/-- Explicit cardinality cost rather than treating poles as invertible. -/
theorem union_with_poles (S poles : Finset I) (b p : Nat)
    (hs : S.card ≤ b) (hp : poles.card ≤ p) : (S∪poles).card ≤ b+p :=
  (Finset.card_union_le S poles).trans (Nat.add_le_add hs hp)

#print axioms joint_failure_in_support
#print axioms equality_outside_union
end
end AspisV8Completion.CommonSupport
