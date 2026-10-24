import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6StdByteSlice

private theorem list_eq_run {T : Type} [DecidableEq T] (xs ys : List T) :
    (if xs.length=ys.length then
      List.allM (fun pair : T×T => ok (decide (pair.1=pair.2))) (xs.zip ys)
      else ok false) = ok (decide (xs=ys)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [List.allM] <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      by_cases hxy : x=y
      · subst y
        simpa [List.allM,bind_tc_ok] using ih ys
      · simp [List.allM,bind_tc_ok,hxy] <;> (intro _; rfl)

private theorem byte_callback (x y : U8) :
    (do let b ← core.cmp.PartialEqU8.ne x y
        ok (decide (¬b=true))) = ok (decide (x=y)) := by
  simp [core.cmp.PartialEqU8,liftFun2,core.cmp.impls.PartialEqU8.ne]
  constructor <;> intro h <;> scalar_tac

/-- Exact total byte-slice comparison, including unequal lengths. -/
theorem eq_exact (a b : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a b =
      ok (decide (a.val=b.val)) := by
  unfold core.slice.cmp.PartialEqSlice.eq
  have hfun :
      (fun pair : U8×U8 => match pair with | (x,y) => do
        let b ← core.cmp.PartialEqU8.ne x y
        ok (decide (¬b=true))) =
      (fun pair : U8×U8 => ok (decide (pair.1=pair.2))) := by
    funext pair
    rcases pair with ⟨x,y⟩
    exact byte_callback x y
  rw [hfun]
  exact list_eq_run a.val b.val

@[step] theorem eq_spec (a b : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a b
      ⦃ result => result=true ↔ a=b ⦄ := by
  rw [eq_exact,WP.spec_ok]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    cases a
    cases b
    cases h
    rfl
  · intro h
    cases h
    rfl

#print axioms eq_exact
#print axioms eq_spec
end AspisS6StdByteSlice
