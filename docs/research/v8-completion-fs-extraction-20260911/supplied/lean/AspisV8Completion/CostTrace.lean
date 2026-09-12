/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.CostTrace
variable {Op : Type*}

/-- Cost model supplied by the pinned runtime/calibration. This file is only
integer accounting; the unit bounds and trace correspondence are not proved. -/
def cost (unit : Op → Nat) (trace : List Op) : Nat := (trace.map unit).sum

theorem cost_append (unit : Op → Nat) (left right : List Op) :
    cost unit (left++right) = cost unit left+cost unit right := by
  simp [cost]

theorem cost_le_steps (unit : Op → Nat) (trace : List Op) (bound : Nat)
    (each : ∀ op ∈ trace, unit op ≤ bound) : cost unit trace ≤ trace.length*bound := by
  induction trace with
  | nil => simp [cost]
  | cons op rest ih =>
    have first := each op (by simp)
    have tail := ih (fun x hx => each x (by simp [hx]))
    simp only [cost, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

theorem fits (known tail limit : Nat) (tailBound : tail ≤ limit-known-1)
    (headroom : known < limit) : known+tail < limit := by omega

#print axioms cost_le_steps
end AspisV8Completion.CostTrace
