/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.UnresolvedTargets
noncomputable section
variable {D : Type*} [DecidableEq D]

/-- A harmless default adds a possible extra target but never removes a real
one. There are at most N images even when opening indices are chosen later. -/
def targetSet {N : Nat} (resolver : Fin N → Option D) (fallback : D) : Finset D :=
  Finset.univ.image (fun i => (resolver i).getD fallback)

theorem card_targetSet {N : Nat} (resolver : Fin N → Option D) (fallback : D) :
    (targetSet resolver fallback).card ≤ N := by
  exact (Finset.card_image_le).trans (by simp)

theorem actual_target_member {N : Nat} (resolver : Fin N → Option D)
    (fallback target : D) (i : Fin N) (resolved : resolver i = some target) :
    target ∈ targetSet resolver fallback := by
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_univ _, by simp [resolved]⟩

theorem two_phase_cap {N : Nat} (first second : Fin N → Option D) (fallback : D) :
    (targetSet first fallback ∪ targetSet second fallback).card ≤ 2*N := by
  have one := card_targetSet first fallback
  have two := card_targetSet second fallback
  have both := Finset.card_union_le (targetSet first fallback) (targetSet second fallback)
  omega

/-- Adaptively choosing the position does not increase a PREFIX-FIXED
whole-domain target set. Prefix fixation itself is not proved by this lemma. -/
theorem selected_late_hit_covered {N : Nat} {Input : Type*}
    (resolver : Fin N → Option D) (fallback : D) (hash : Input → D)
    (i : Fin N) (target : D) (input : Input)
    (resolved : resolver i = some target) (hit : hash input = target) :
    hash input ∈ targetSet resolver fallback := by
  rw [hit]
  exact actual_target_member resolver fallback target i resolved

#print axioms two_phase_cap
#print axioms selected_late_hit_covered
end
end AspisV8Completion.UnresolvedTargets
