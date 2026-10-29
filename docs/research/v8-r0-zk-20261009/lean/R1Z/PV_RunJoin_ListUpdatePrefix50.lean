import Mathlib.Data.List.Basic
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ListUpdatePrefix50

theorem complete {A : Type} (xs : List A) (i : Nat) (v : A) (bound : i<xs.length) :
    (xs.set i v).take (i+1)=xs.take i ++ [v] := by
  induction xs generalizing i with
  | nil => simp only [List.length_nil] at bound;omega
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hi : i<xs.length := by simp only [List.length_cons] at bound;omega
      change x :: (xs.set i v).take (i+1)=x :: (xs.take i ++ [v])
      rw [ih i hi]
#print axioms complete
end R1Z.PV_RunJoin_ListUpdatePrefix50
