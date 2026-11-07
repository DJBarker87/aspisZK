import Aeneas
set_option autoImplicit false
namespace NMX_R3_ListRead
/-- A bounded coordinate never observes a default value. -/
theorem getD {α : Type} (xs : List α) (i : Nat) (bound : i < xs.length) (d : α) :
 xs.getD i d = xs[i] := by
 induction xs generalizing i with
 | nil => simp only [List.length_nil] at bound; omega
 | cons x xs ih =>
   cases i with
   | zero => rfl
   | succ i => exact ih i (by simpa using bound)
#print axioms getD
end NMX_R3_ListRead
