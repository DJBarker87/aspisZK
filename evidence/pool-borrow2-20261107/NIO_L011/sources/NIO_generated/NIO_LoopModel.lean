import NIO_AbortScopes
set_option autoImplicit false
namespace NIO_LoopModel
open NIO_Nested

structure State where
  held : List Nat
  counter : Nat → Int

/-- Counter/reference model of the one original acquisition-and-push statement.
The error arm is specifically AccountBorrowFailed; state is retained for its frame. -/
def step (s : State) (cell : Nat) : Bool × State :=
  if s.counter cell = 0 then
    (true,⟨s.held ++ [cell],put s.counter cell (-1)⟩)
  else (false,s)

theorem failed_step (s : State) (cell : Nat) (busy : s.counter cell ≠ 0) :
    step s cell = (false,s) := by simp [step,busy]
#print axioms failed_step

theorem successful_step (s : State) (cell : Nat) (free : s.counter cell = 0) :
    step s cell = (true,⟨s.held ++ [cell],put s.counter cell (-1)⟩) := by
  simp [step,free]
#print axioms successful_step

theorem successful_fresh (s : State) (cell : Nat)
    (prior : ∀ c ∈ s.held, s.counter c = -1) (free : s.counter cell = 0) :
    cell ∉ s.held := (retained_step s.counter s.held cell prior free).1
#print axioms successful_fresh

theorem successful_held_invariant (s : State) (cell : Nat)
    (prior : ∀ c ∈ s.held, s.counter c = -1) (free : s.counter cell = 0) :
    ∀ c ∈ (step s cell).2.held, (step s cell).2.counter c = -1 := by
  rw [successful_step s cell free]
  intro c member
  have split : c ∈ s.held ∨ c = cell := by simpa using member
  rcases split with old | fresh
  · exact (retained_step s.counter s.held cell prior free).2 c old
  · subst c
    simp [put]
#print axioms successful_held_invariant

theorem append_prefix (held : List Nat) (cell : Nat) :
    (held ++ [cell]).take held.length = held := by
  induction held with
  | nil => rfl
  | cons x xs ih =>
    change x :: (xs ++ [cell]).take xs.length = x :: xs
    rw [ih]
#print axioms append_prefix

theorem successful_prefix (s : State) (cell : Nat) (free : s.counter cell = 0) :
    (step s cell).2.held.take s.held.length = s.held := by
  rw [successful_step s cell free]
  exact append_prefix s.held cell
#print axioms successful_prefix
end NIO_LoopModel
