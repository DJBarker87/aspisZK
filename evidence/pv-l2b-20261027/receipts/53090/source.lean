import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace PV_L2B_Guards
-- Mathematical guard laws. Native builder/canonicality/refinement association
-- is retained, never represented by an additional trust item.
def firstFailure : List Bool → Nat
 | [] => 0
 | true :: _ => 1
 | false :: xs => 1+firstFailure xs
theorem passing_trace (n : Nat) : firstFailure (List.replicate n false) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,firstFailure,ih]; omega
#print axioms passing_trace
theorem failed_trace (xs : List Bool) : firstFailure (true::xs) = 1 := rfl
#print axioms failed_trace
theorem zero_guard {A : Type} [Zero A] [DecidableEq A] (x : A) (hx : x=0) : decide (x ≠ 0) = false := by simp [hx]
#print axioms zero_guard
end PV_L2B_Guards
