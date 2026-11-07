import NMT_R2_StdByte
set_option autoImplicit false
namespace NMT_R2_ListEquality
open Aeneas Aeneas.Std NMT_345Std

theorem source (xs ys : List U8) :
 listEq core.cmp.PartialEqU8.eq xs ys = .ok (decide (xs = ys)) := by
 have same : core.cmp.PartialEqU8.eq = eqByte :=
  funext (fun x => funext (fun y => NMT_R2_StdByte.native x y))
 rw [same]
 induction xs generalizing ys with
 | nil => cases ys <;> rfl
 | cons x xs ih =>
  cases ys with
  | nil => rfl
  | cons y ys =>
   simp only [listEq,eqByte,bind_tc_ok]
   by_cases h : x = y
   · subst y
     simp only [decide_true,if_true,List.cons.injEq,true_and]
     exact ih ys
   · simp only [h,decide_false,Bool.false_eq_true,if_false,List.cons.injEq,false_and]
#print axioms source
end NMT_R2_ListEquality
