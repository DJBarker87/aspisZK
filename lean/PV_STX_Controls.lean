import PV_STX_PrefixLaws
set_option autoImplicit false
namespace PV_STX_Controls
open Aeneas Aeneas.Std PV_STX_Code PV_STX_Machine PV_STX_PrefixLaws

inductive Request : Type → Type 1 where
  | draw : Request Bool

def answers : Handler Request Nat Nat := fun op cursor => match op with
  | .draw => ⟨.returned (.ok (cursor != 0)),cursor+1,[cursor]⟩

def retryBody (_ : Unit) : Code Request (ControlFlow Unit Unit) := do
  let accepted ← Code.call Request.draw
  if accepted then pure (.done ()) else pure (.cont ())

def retry : Code Request Unit := .loop retryBody ()

/-- A small operational control, NOT a deployed-source/native fixture:
identical requests reject then succeed because the shared world advances. -/
theorem reject_then_success : run answers 9 retry 0 = ⟨.returned (.ok ()),2,[0,1]⟩ := by
  rfl

def foreverBody (_ : Unit) : Code Request (ControlFlow Unit Unit) := .result (.ok (.cont ()))
def forever : Code Request Unit := .loop foreverBody ()
def phase0 (w : Nat) : Prefix Request Nat Nat Unit := ⟨.running (start forever),w,[]⟩
def phase1 (w : Nat) : Prefix Request Nat Nat Unit :=
  ⟨.running ⟨_,foreverBody (),.loop foreverBody .done⟩,w,[]⟩

theorem step_phase0 (w : Nat) : advance answers 1 (phase0 w) = phase1 w := rfl

theorem step_phase1 (w : Nat) : advance answers 1 (phase1 w) = phase0 w := rfl

/-- Every finite prefix of this infinite source loop is represented by its
actual continuation. No fuel value turns it into a source div/error. -/
theorem forever_prefix (n w : Nat) :
    run answers n forever w = phase0 w ∨ run answers n forever w = phase1 w := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    change advance answers (n+1) (phase0 w) = phase0 w ∨
      advance answers (n+1) (phase0 w) = phase1 w
    rw [advance_add]
    cases ih with
    | inl h => exact Or.inr (by rw [show advance answers n (phase0 w) = phase0 w from h]; rfl)
    | inr h => exact Or.inl (by rw [show advance answers n (phase0 w) = phase1 w from h]; rfl)

theorem forever_never_returns (n w : Nat) (r : Result Unit) :
    (run answers n forever w).status ≠ .returned r := by
  cases forever_prefix n w with
  | inl h => rw [h]; intro h; cases h
  | inr h => rw [h]; intro h; cases h

#print axioms reject_then_success
#print axioms step_phase0
#print axioms step_phase1
#print axioms forever_prefix
#print axioms forever_never_returns
end PV_STX_Controls
