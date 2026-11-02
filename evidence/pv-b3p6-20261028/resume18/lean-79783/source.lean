import PV_B3P_PreconditionFormatting569227
namespace PV_B3P_PanicPatterns571227
open Aeneas Aeneas.Std
set_option autoImplicit false
/-- A control edge to a diagnostic, rather than a model of formatting. -/
def diagnostic (guard : Prop) : Prop := ¬ guard
/-- Both continuations remain arbitrary, including error and divergence. -/
def branch {α : Type} (guard : Prop) [Decidable guard]
    (normal panic : Result α) : Result α := if guard then normal else panic

/-- The common control law; equality of Result values is never used to infer
that a diagnostic edge was absent. -/
theorem guarded_edge {α : Type} (guard : Prop) [Decidable guard]
    (normal first second : Result α) :
    (diagnostic guard → ¬ guard) ∧
    (guard → ¬ diagnostic guard ∧ branch guard normal first = branch guard normal second) := by
  constructor
  · exact fun failed => failed
  · intro safe
    exact ⟨fun failed => failed safe, by simp only [branch, if_pos safe]⟩

structure IndexState where
  index : Nat
  length : Nat

def indexGuard (s : IndexState) : Prop := s.index < s.length
instance (s : IndexState) : Decidable (indexGuard s) := inferInstanceAs (Decidable (s.index < s.length))

theorem index_out_of_bounds {α : Type} (s : IndexState) (normal first second : Result α) :
    (diagnostic (indexGuard s) → ¬ indexGuard s) ∧
    (indexGuard s → ¬ diagnostic (indexGuard s) ∧
      branch (indexGuard s) normal first = branch (indexGuard s) normal second) :=
  guarded_edge _ normal first second

structure SliceState where
  first : Nat
  last : Nat
  length : Nat

def sliceGuard (s : SliceState) : Prop := s.first ≤ s.last ∧ s.last ≤ s.length
instance (s : SliceState) : Decidable (sliceGuard s) :=
  inferInstanceAs (Decidable (s.first ≤ s.last ∧ s.last ≤ s.length))

theorem slice_range {α : Type} (s : SliceState) (normal first second : Result α) :
    (diagnostic (sliceGuard s) → ¬ sliceGuard s) ∧
    (sliceGuard s → ¬ diagnostic (sliceGuard s) ∧
      branch (sliceGuard s) normal first = branch (sliceGuard s) normal second) :=
  guarded_edge _ normal first second

inductive ArithmeticState where
  | add (left right maximum : Nat)
  | sub (left right : Nat)

def arithmeticGuard : ArithmeticState → Prop
  | .add left right maximum => left + right ≤ maximum
  | .sub left right => right ≤ left
instance (s : ArithmeticState) : Decidable (arithmeticGuard s) := by
  cases s <;> unfold arithmeticGuard <;> infer_instance

theorem arithmetic_overflow {α : Type} (s : ArithmeticState) (normal first second : Result α) :
    (diagnostic (arithmeticGuard s) → ¬ arithmeticGuard s) ∧
    (arithmeticGuard s → ¬ diagnostic (arithmeticGuard s) ∧
      branch (arithmeticGuard s) normal first = branch (arithmeticGuard s) normal second) :=
  guarded_edge _ normal first second

def optionGuard {β : Type} (s : Option β) : Prop := s.isSome = true
instance {β : Type} (s : Option β) : Decidable (optionGuard s) :=
  inferInstanceAs (Decidable (s.isSome = true))

theorem unwrap_expect {α β : Type} (s : Option β) (normal first second : Result α) :
    (diagnostic (optionGuard s) → ¬ optionGuard s) ∧
    (optionGuard s → ¬ diagnostic (optionGuard s) ∧
      branch (optionGuard s) normal first = branch (optionGuard s) normal second) :=
  guarded_edge _ normal first second

/-- For an explicit panic, safe is the *source caller's* avoidance predicate.
This theorem does not establish that predicate. -/
theorem explicit_panic {α : Type} (safe : Bool) (normal first second : Result α) :
    (diagnostic (safe = true) → safe ≠ true) ∧
    (safe = true → ¬ diagnostic (safe = true) ∧
      branch (safe = true) normal first = branch (safe = true) normal second) :=
  guarded_edge _ normal first second

theorem assertion {α : Type} (condition expected : Bool) (normal first second : Result α) :
    (diagnostic (condition = expected) → condition ≠ expected) ∧
    (condition = expected → ¬ diagnostic (condition = expected) ∧
      branch (condition = expected) normal first = branch (condition = expected) normal second) :=
  guarded_edge _ normal first second

/-- Generic induction over finite source-event reachability. Its entry,
preservation, and observation links must be supplied from the actual source;
this is a reusable lemma, not a newly asserted endpoint invariant. -/
inductive Reachable {State : Type} (entry : State → Prop) (step : State → State → Prop) : State → Prop
  | initial {s : State} : entry s → Reachable entry step s
  | next {s t : State} : Reachable entry step s → step s t → Reachable entry step t

theorem reachable_guard {State : Type} (entry : State → Prop) (step : State → State → Prop)
    (invariant guard : State → Prop)
    (initial : ∀ s, entry s → invariant s)
    (preserved : ∀ s t, invariant s → step s t → invariant t)
    (observed : ∀ s, invariant s → guard s) :
    ∀ s, Reachable entry step s → guard s := by
  intro s reached
  apply observed s
  induction reached with
  | initial h => exact initial _ h
  | next _ edge ih => exact preserved _ _ ih edge

#print axioms guarded_edge
#print axioms index_out_of_bounds
#print axioms slice_range
#print axioms arithmetic_overflow
#print axioms unwrap_expect
#print axioms explicit_panic
#print axioms assertion
#print axioms reachable_guard
end PV_B3P_PanicPatterns571227
