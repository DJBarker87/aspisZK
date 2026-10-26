import Std

namespace R1Z.PV_CB3_PoleRows
set_option autoImplicit false

/-- Ordered Boolean composition used after the extracted row reads succeed.
The source's mask-index failures are handled by the Result-level source law. -/
def scan {α : Type} (test : α → Bool) : Bool → List α → Bool
  | clear, [] => clear
  | clear, value :: rest => scan test (clear && test value) rest

theorem scan_value {α : Type} (test : α → Bool) (clear : Bool) (xs : List α) :
    scan test clear xs = (clear && xs.all test) := by
  induction xs generalizing clear with
  | nil => simp only [scan, List.all_nil, Bool.and_true]
  | cons x xs ih =>
    simp only [scan, ih, List.all_cons, Bool.and_assoc]

theorem scan_append {α : Type} (test : α → Bool) (clear : Bool) (xs ys : List α) :
    scan test clear (xs ++ ys) = scan test (scan test clear xs) ys := by
  induction xs generalizing clear with
  | nil => rfl
  | cons x xs ih => exact ih (clear && test x)

theorem scan_absorbing {α : Type} (test : α → Bool) (xs : List α) :
    scan test false xs = false := by
  rw [scan_value]
  rfl

theorem scan_inactive {α : Type} (clear : Bool) (xs : List α) :
    scan (fun _ => true) clear xs = clear := by
  induction xs generalizing clear with
  | nil => rfl
  | cons x xs ih => simp only [scan, Bool.and_true, ih]

#print axioms scan_value
#print axioms scan_append
#print axioms scan_absorbing
#print axioms scan_inactive
end R1Z.PV_CB3_PoleRows
