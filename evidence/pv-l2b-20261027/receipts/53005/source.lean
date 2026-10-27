import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Capped rejection at the Option-candidate interface. `none` means reject;
`some a` means accept a. The uniform-word association is a separate obligation. -/
set_option autoImplicit false
namespace PV_L2B_Rejection

def scan {A : Type} : Nat → List (Option A) → Nat × Option A
  | 0, _ => (0, none)
  | _ + 1, [] => (0, none)
  | n + 1, none :: xs => let r := scan n xs; (r.1 + 1, r.2)
  | _ + 1, some a :: _ => (1, some a)

theorem cap_zero {A : Type} (xs : List (Option A)) : scan 0 xs = (0, none) := rfl
#print axioms cap_zero
theorem empty {A : Type} (n : Nat) : scan (n+1) ([] : List (Option A)) = (0, none) := rfl
#print axioms empty
theorem accepted {A : Type} (n : Nat) (a : A) (xs : List (Option A)) : scan (n+1) (some a :: xs) = (1, some a) := rfl
#print axioms accepted
theorem rejected {A : Type} (n : Nat) (xs : List (Option A)) : scan (n+1) (none :: xs) = ((scan n xs).1+1, (scan n xs).2) := rfl
#print axioms rejected
theorem consumed_le_cap {A : Type} (n : Nat) (xs : List (Option A)) : (scan n xs).1 ≤ n := by
  induction n generalizing xs with
  | zero => simp [scan]
  | succ n ih =>
    cases xs with
    | nil => simp [scan]
    | cons x xs => cases x <;> simp [scan]; exact ih xs
#print axioms consumed_le_cap
end PV_L2B_Rejection
