import NMT_345EqByte
set_option autoImplicit false
noncomputable section
namespace NMT_345Std
open Aeneas Aeneas.Std Result

theorem bytes_eq (xs ys : List U8) :
 listEq eqByte xs ys = .ok (decide (xs = ys)) := by
 induction xs generalizing ys with
 | nil => cases ys <;> rfl
 | cons x xs ih =>
  cases ys with
  | nil => rfl
  | cons y ys =>
   unfold listEq eqByte
   simp only [bind_tc_ok]
   by_cases h : x = y
   · subst y
     simp only [decide_true,if_true,List.cons.injEq,true_and]
     rw [← eqByte_form]
     exact ih ys
   · simp [h]


#print axioms bytes_eq
end NMT_345Std
