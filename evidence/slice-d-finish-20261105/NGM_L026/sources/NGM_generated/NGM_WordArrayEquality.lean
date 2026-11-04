import Aeneas
set_option autoImplicit false
noncomputable section
namespace NGM_WordArrayEquality
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem word (x y : U32) : core.cmp.PartialEqU32.eq x y=ok (decide (x=y)) := by
 simp [core.cmp.PartialEqU32]

theorem lists (xs ys : List U32) (lengths : xs.length=ys.length) :
 List.allM (fun (x,y)=>do
  let different ← core.cmp.PartialEqU32.ne x y
  ok (decide (¬different=true))) (xs.zip ys)=ok (decide (xs=ys)) := by
 induction xs generalizing ys with
 | nil => cases ys <;> simp_all [List.allM,pure]
 | cons x xs ih =>
  cases ys with
  | nil => simp_all
  | cons y ys =>
   have tail : xs.length=ys.length := by simpa using lengths
   rw [List.zip_cons_cons]
   simp only [List.allM]
   have element : (do let different ← core.cmp.PartialEqU32.ne x y
                      ok (decide (¬different=true)))=ok (decide (x=y)) := by
    simp [core.cmp.PartialEqU32,core.cmp.PartialEq.ne.trait_default,
     core.cmp.PartialEq.ne.default,word]
   rw [element]
   by_cases same : x=y
   · simp only [same,decide_true,bind_tc_ok,if_pos]
     simpa only [List.cons.injEq,true_and,liftFun2,bind_tc_ok] using ih ys tail
   · simp [same,pure]

theorem arrays {n : Usize} (a b : Array U32 n) :
 core.array.equality.PartialEqArray.eq core.cmp.PartialEqU32 a b=ok (decide (a=b)) := by
 unfold core.array.equality.PartialEqArray.eq
 have lengths : a.length=b.length := by have:=a.property;have:=b.property;scalar_tac
 rw [if_pos lengths,lists a.val b.val (by have:=a.property;have:=b.property;scalar_tac)]
 have equal : (a.val=b.val)↔a=b := ⟨Subtype.ext,fun h=>congrArg Subtype.val h⟩
 simp only [equal]

theorem arrays_ne {n : Usize} (a b : Array U32 n) :
 core.array.equality.PartialEqArray.ne core.cmp.PartialEqU32 a b=ok (decide (a≠b)) := by
 simp [core.array.equality.PartialEqArray,core.cmp.PartialEq.ne.trait_default,
  core.cmp.PartialEq.ne.default,arrays]
#print axioms word
#print axioms lists
#print axioms arrays
#print axioms arrays_ne
end NGM_WordArrayEquality
end
