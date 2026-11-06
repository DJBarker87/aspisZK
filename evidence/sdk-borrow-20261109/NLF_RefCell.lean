import Mathlib.Data.List.Nodup
import Mathlib.Tactic
set_option autoImplicit false
namespace NLF_RefCell
/-- One cell owns its complete token set. Exclusive tokens cannot be duplicated;
shared tokens are unique, and a writer excludes every reader. -/
structure Cell (α : Type) where
  payload : α
  readers : List Nat
  writer : Option Nat
  deriving DecidableEq

def Valid {α : Type} (c : Cell α) : Prop :=
  c.readers.Nodup ∧ (c.writer ≠ none → c.readers = [])

def flag {α : Type} (c : Cell α) : Int :=
  match c.writer with | some _ => -1 | none => Int.ofNat c.readers.length

inductive Error where | conflict | invalidToken deriving DecidableEq
inductive Kind where | shared | exclusive deriving DecidableEq
structure Guard where
  cell : Nat
  token : Nat
  kind : Kind
  deriving DecidableEq

def shared {α : Type} (c : Cell α) (t : Nat) : Except Error (Cell α) :=
  if c.writer = none ∧ c.readers.length < 9223372036854775807 ∧ t ∉ c.readers then
    .ok { c with readers := t :: c.readers }
  else .error .conflict

def exclusive {α : Type} (c : Cell α) (t : Nat) : Except Error (Cell α) :=
  if c.writer = none ∧ c.readers = [] then
    .ok { c with writer := some t }
  else .error .conflict

/-- Drop consumes a token; a second drop is rejected rather than corrupting a counter.
The invalidToken branch is unreachable for a live typed Rust guard. -/
def dropShared {α : Type} (c : Cell α) (t : Nat) : Except Error (Cell α) :=
  if c.writer = none ∧ t ∈ c.readers then .ok {c with readers := c.readers.erase t}
  else .error .invalidToken

def dropExclusive {α : Type} (c : Cell α) (t : Nat) : Except Error (Cell α) :=
  if c.writer = some t then .ok {c with writer := none}
  else .error .invalidToken

def live {α : Type} (c : Cell α) (t : Nat) (k : Kind) : Prop :=
  match k with | .shared => c.writer = none ∧ t ∈ c.readers
               | .exclusive => c.writer = some t

/-- Ref::map and RefMut::map change the view, retaining the same ownership token. -/
structure View (β : Type) where
  guard : Guard
  value : β

def mapView {α β : Type} (f : α → β) (v : View α) : View β := ⟨v.guard, f v.value⟩

theorem map_token {α β : Type} (f : α → β) (v : View α) :
    (mapView f v).guard = v.guard := rfl

theorem shared_valid {α : Type} (c : Cell α) (t : Nat) (v : Valid c)
    (fresh : t ∉ c.readers) (free : c.writer = none)
    (bound : c.readers.length < 9223372036854775807) :
    shared c t = .ok {c with readers := t :: c.readers} ∧
    Valid {c with readers := t :: c.readers} := by
  constructor
  · simp [shared, fresh, free, bound]
  · exact ⟨List.nodup_cons.mpr ⟨fresh, v.1⟩, by simp [free]⟩

theorem exclusive_valid {α : Type} (c : Cell α) (t : Nat)
    (free : c.writer = none) (empty : c.readers = []) :
    exclusive c t = .ok {c with writer := some t} ∧
    Valid {c with writer := some t} := by
  simp [exclusive, free, empty, Valid]

theorem exclusive_conflict {α : Type} (c : Cell α) (t : Nat)
    (busy : c.writer ≠ none ∨ c.readers ≠ []) : exclusive c t = .error .conflict := by
  rcases busy with h | h <;> simp [exclusive, h]

theorem shared_conflict {α : Type} (c : Cell α) (t : Nat)
    (busy : c.writer ≠ none) : shared c t = .error .conflict := by
  simp [shared, busy]

#print axioms map_token
#print axioms shared_valid
#print axioms exclusive_valid
#print axioms exclusive_conflict
#print axioms shared_conflict
end NLF_RefCell
