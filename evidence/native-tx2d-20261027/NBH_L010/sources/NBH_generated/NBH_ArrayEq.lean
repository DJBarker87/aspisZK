import NBH_Frontier
set_option autoImplicit false
namespace NBH_ArrayEq
open Aeneas Aeneas.Std Result

theorem list_eq (xs ys : List U8) (hlen : xs.length = ys.length) :
    List.allM (fun (x,y) => do
      let b ← core.cmp.PartialEqU8.ne x y
      ok (decide (¬ b = true))) (xs.zip ys) = ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [List.allM]
  | cons x xs ih =>
    cases ys with
    | nil => simp_all
    | cons y ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      simp [List.allM,core.cmp.PartialEqU8,core.cmp.impls.PartialEqU8.ne,
        core.cmp.liftFun2,ih ys hlen]

theorem source {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok (decide (a=b)) := by
  unfold core.array.equality.PartialEqArray.eq
  have length : a.length=b.length := by have := a.property; have := b.property; scalar_tac
  rw [if_pos length, list_eq a.val b.val (by have := a.property; have := b.property; scalar_tac)]
  simp only [Subtype.ext_iff]

#print axioms list_eq
#print axioms source
end NBH_ArrayEq
