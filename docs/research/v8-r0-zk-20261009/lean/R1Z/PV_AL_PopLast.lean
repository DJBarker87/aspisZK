import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_PopLast
set_option autoImplicit false

theorem last {T : Type} (xs : List T) (h : xs≠[]) :
    xs.getLast?=some (xs[xs.length-1]'(by cases xs <;> simp_all)) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simpa only [List.getLast?_cons_cons,List.length_cons,Nat.add_sub_cancel,
        List.getElem_cons_succ] using ih (by simp)

theorem dropLast {T : Type} (xs : List T) : xs.dropLast=xs.take (xs.length-1) := by
  exact List.dropLast_eq_take
#print axioms last
#print axioms dropLast
end R1Z.PV_AL_PopLast
