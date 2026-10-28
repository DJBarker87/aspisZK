import NBH_Frontier
set_option autoImplicit false
noncomputable section
namespace NBH_ArrayEq
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem list_eq (xs ys : List U8) (hlen : xs.length = ys.length) :
    List.allM (fun (x,y) => do
      let b ← core.cmp.PartialEqU8.ne x y
      ok (decide (¬ b = true))) (xs.zip ys) = ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [List.allM,pure]
  | cons x xs ih =>
    cases ys with
    | nil => simp_all
    | cons y ys =>
      have tail : xs.length=ys.length := by simpa using hlen
      rw [List.zip_cons_cons]
      simp only [List.allM]
      have eqv : (do let b ← core.cmp.PartialEqU8.ne x y; ok (decide (¬ b = true))) = ok (decide (x=y)) := by
        simp [core.cmp.PartialEqU8,core.cmp.impls.PartialEqU8.ne]
        congr 2
        scalar_tac
      rw [eqv]
      by_cases same : x=y
      · simp only [same,decide_true,bind_tc_ok,if_pos]
        simpa only [List.cons.injEq, true_and] using ih ys tail
      · simp [same,pure]

theorem source {n : Usize} (a b : Array U8 n) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok (decide (a=b)) := by
  unfold core.array.equality.PartialEqArray.eq
  have length : a.length=b.length := by have := a.property; have := b.property; scalar_tac
  rw [if_pos length, list_eq a.val b.val (by have := a.property; have := b.property; scalar_tac)]
  congr 1
  exact propext (by constructor; exact Array.ext; intro h; exact congrArg (fun x => x.val) h)

#print axioms list_eq
#print axioms source
end NBH_ArrayEq
