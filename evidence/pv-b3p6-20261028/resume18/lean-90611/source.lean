import PV_B3P_CounterGuards571227
namespace PV_B3P_InitializerEvents578227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
set_option autoImplicit false

/-- Observations stop BEFORE the requested diagnostic-capable instruction.
Failures/divergence before that point remain failures/divergence. Operations
following that point are deliberately not evaluated. Private numeric fields
are separate from the arbitrary generator/buffer world; the source frame
checker must establish that no capability to these stack fields escapes. -/
inductive Site where
  | indexPrecondition
  | index
  | addPrecondition
  deriving DecidableEq

structure Effects (α β γ : Type) where
  generate : Usize → Result α
  tryBranch : α → Result (ControlFlow γ β)
  indexCheck : Result Unit
  indexAccess : Result Unit
  write : γ → Result Unit
  inhabited : Result Unit
  ubChecks : Bool

def through : List (Result Unit) → Option IndexState → Result (Option IndexState)
  | [], answer => .ok answer
  | effect :: rest, answer => do
    let _ ← effect
    through rest answer

def afterBranch {α β γ : Type} (site : Site) (count length : Usize)
    (effects : Effects α β γ) (value : γ) : Result (Option IndexState) :=
  let state := some ⟨count.val,length.val⟩
  let check := if effects.ubChecks then effects.indexCheck else .ok ()
  match site with
  | .indexPrecondition => through [] (if effects.ubChecks then state else none)
  | .index => through [check] state
  | .addPrecondition => through [check,effects.indexAccess,effects.write value,effects.inhabited]
      (if effects.ubChecks then state else none)

def sourceEvent {α β γ : Type} (site : Site) (count length : Usize)
    (effects : Effects α β γ) : Result (Option IndexState) := do
  if count.val < length.val then
    let generated ← effects.generate count
    let branched ← effects.tryBranch generated
    match branched with
    | .done _ => .ok none
    | .cont value => afterBranch site count length effects value
  else .ok none

/-- Prefixes built from a private-field observation cannot forge a different
state. This is proved for all effect answers, including fail and div. -/
theorem bind_observation {α : Type} (effect : Result α)
    (next : α → Result (Option IndexState)) (expected observed : IndexState)
    (preserved : ∀ value, next value = .ok (some observed) → observed = expected)
    (ran : (do let value ← effect; next value) = .ok (some observed)) :
    observed = expected := by
  cases effect with
  | ok value => exact preserved value ran
  | fail error => cases ran
  | div => cases ran

theorem through_value (effects : List (Result Unit)) (answer : Option IndexState)
    (observed : IndexState) (ran : through effects answer = .ok (some observed)) :
    answer = some observed := by
  induction effects with
  | nil => cases ran; rfl
  | cons effect rest ih =>
    cases effect with
    | ok value => exact ih ran
    | fail error => cases ran
    | div => cases ran

theorem afterBranch_frame {α β γ : Type} (site : Site) (count length : Usize)
    (effects : Effects α β γ) (value : γ) (observed : IndexState)
    (ran : afterBranch site count length effects value = .ok (some observed)) :
    observed = ⟨count.val,length.val⟩ := by
  cases site <;> cases h : effects.ubChecks <;>
    simp only [afterBranch, h, Bool.false_eq_true, if_false, if_true] at ran
  all_goals have equal := through_value _ _ _ ran
  all_goals cases equal
  all_goals rfl

/-- The observed guard follows from the EXECUTED loop test and the checked
private frame, not from an assumed guard or a whole-function success. Each
iteration rechecks the test, so this holds at any private count/metadata. -/
theorem event_guard {α β γ : Type} (site : Site) (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceEvent site count length effects = .ok (some observed)) :
    indexGuard observed := by
  by_cases active : count.val < length.val
  · simp only [sourceEvent, if_pos active] at ran
    have frame : observed = ⟨count.val,length.val⟩ := by
      apply bind_observation _ _ _ _ _ ran
      intro generated next
      apply bind_observation _ _ _ _ _ next
      intro branched last
      cases branched with
      | done residual => cases last
      | cont value => exact afterBranch_frame site count length effects value observed last
    rw [frame]
    exact active
  · simp only [sourceEvent, if_neg active] at ran
    cases ran

theorem event_index_certificate {α β γ δ : Type} (site : Site) (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceEvent site count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  (index_out_of_bounds observed normal first second).2 (event_guard site count length effects observed ran)

theorem event_add_guard {α β γ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceEvent .addPrecondition count length effects = .ok (some observed)) :
    arithmeticGuard (.add observed.index 1 (UScalar.max .Usize)) := by
  have inside := event_guard .addPrecondition count length effects observed ran
  have frame : observed = ⟨count.val,length.val⟩ := by
    by_cases active : count.val < length.val
    · simp only [sourceEvent, if_pos active] at ran
      apply bind_observation _ _ _ _ _ ran
      intro generated next
      apply bind_observation _ _ _ _ _ next
      intro branched last
      cases branched with
      | done residual => cases last
      | cont value => exact afterBranch_frame .addPrecondition count length effects value observed last
    · simp only [sourceEvent, if_neg active] at ran
      cases ran
  rw [frame] at inside ⊢
  exact (PV_B3P_PreconditionFormatting569227.initializer_conditions count length inside).2.1

theorem event_add_certificate {α β γ δ : Type} (count length : Usize)
    (effects : Effects α β γ) (observed : IndexState)
    (ran : sourceEvent .addPrecondition count length effects = .ok (some observed))
    (normal first second : Result δ) :
    ¬ diagnostic (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) ∧
      branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal first =
        branch (arithmeticGuard (.add observed.index 1 (UScalar.max .Usize))) normal second :=
  (arithmetic_overflow _ normal first second).2 (event_add_guard count length effects observed ran)

#print axioms bind_observation
#print axioms through_value
#print axioms afterBranch_frame
#print axioms event_guard
#print axioms event_index_certificate
#print axioms event_add_guard
#print axioms event_add_certificate
end PV_B3P_InitializerEvents578227
