import Init
set_option autoImplicit false
namespace PCF_Count

inductive Reply where
  | ok | notEnoughKeys | invalidArgument
  deriving DecidableEq

/-- Full source order, with count represented by the slice's own length. -/
def source (count expected : Nat) : Reply :=
  if count ≠ expected then
    if count < expected then .notEnoughKeys else .invalidArgument
  else .ok

/-- PCA/PCC count reference, including both rejection arms. -/
def reference (count expected : Nat) : Reply :=
  if count = expected then .ok else
    if count < expected then .notEnoughKeys else .invalidArgument

theorem complete (count expected : Nat) : source count expected = reference count expected := by
  by_cases h : count = expected <;> simp [source, reference, h]

theorem admitted_count (count expected : Nat) :
    source count expected = .ok ↔ count = expected := by
  by_cases h : count = expected <;> simp [source, h]

theorem fewer (count expected : Nat) (h : count < expected) :
    source count expected = .notEnoughKeys := by
  have ne : count ≠ expected := Nat.ne_of_lt h
  simp [source, ne, h]

theorem extra (count expected : Nat) (h : expected < count) :
    source count expected = .invalidArgument := by
  have ne : count ≠ expected := (Nat.ne_of_lt h).symm
  have nl : ¬ count < expected := Nat.not_lt_of_ge (Nat.le_of_lt h)
  simp [source, ne, nl]

/-- The count check cannot modify accounts or emit any effect on any arm. -/
def execution {State Event : Type} (count expected : Nat) (s : State) :
    Reply × State × List Event := (source count expected, s, [])

theorem result_state_effects {State Event : Type} (count expected : Nat) (s : State) :
    execution (Event := Event) count expected s = (reference count expected, s, []) := by
  simp only [execution, complete]

#print axioms complete
#print axioms admitted_count
#print axioms fewer
#print axioms extra
#print axioms result_state_effects
end PCF_Count
