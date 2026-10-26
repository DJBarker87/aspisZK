import PoolW_Store
set_option autoImplicit false
namespace AspisR1.PoolU_Step
open Aeneas Aeneas.Std Result

/-- A source cut returns its state even on error/divergence. S includes every
observable effect; bind never discards an already executed prefix. This is a
reference carrier, not a native interpreter or an adopted runtime contract. -/
abbrev Step (S E A : Type) := S → Result (core.result.Result A E) × S

def pure {S E A : Type} (a : A) : Step S E A := fun s => (ok (.Ok a),s)

def bind {S E A B : Type} (first : Step S E A) (next : A → Step S E B) : Step S E B :=
  fun s => match first s with
  | (ok (.Ok a),t) => next a t
  | (ok (.Err e),t) => (ok (.Err e),t)
  | (.fail e,t) => (.fail e,t)
  | (.div,t) => (.div,t)

theorem accepted_bind {S E A B : Type} (first : Step S E A) (next : A → Step S E B)
    (s t : S) (b : B) :
    bind first next s = (ok (.Ok b),t) ↔
      ∃ a u, first s = (ok (.Ok a),u) ∧ next a u = (ok (.Ok b),t) := by
  cases h : first s with
  | mk r u =>
    cases r with
    | fail e => simp [bind,h]
    | div => simp [bind,h]
    | ok r =>
      cases r with
      | Err e => simp [bind,h]
      | Ok a => simp [bind,h]

theorem error_prefix {S E A B : Type} (first : Step S E A) (next : A → Step S E B)
    (s t : S) (e : E) (h : first s = (ok (.Err e),t)) :
    bind first next s = (ok (.Err e),t) := by simp [bind,h]

theorem failure_prefix {S E A B : Type} (first : Step S E A) (next : A → Step S E B)
    (s t : S) (e : Error) (h : first s = (.fail e,t)) :
    bind first next s = (.fail e,t) := by simp [bind,h]

theorem divergence_prefix {S E A B : Type} (first : Step S E A) (next : A → Step S E B)
    (s t : S) (h : first s = (.div,t)) :
    bind first next s = (.div,t) := by simp [bind,h]

#print axioms accepted_bind
#print axioms error_prefix
#print axioms failure_prefix
#print axioms divergence_prefix
end AspisR1.PoolU_Step
