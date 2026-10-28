import NBH_ArrayEq
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NBN_WordArrayEq
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem list_eq (xs ys : List U32) (hlen : xs.length = ys.length) :
    List.allM (fun (x,y) => do
      let b ← AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x y
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
      have eqv : (do let b ← AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x y; ok (decide (¬ b = true))) = ok (decide (x=y)) := by
        simp [AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31,core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]
      rw [eqv]
      by_cases same : x=y
      · simp only [same,decide_true,bind_tc_ok,if_pos]
        simpa only [List.cons.injEq, true_and, liftFun2, bind_tc_ok] using ih ys tail
      · simp [same,pure]

theorem source {n : Usize} (a b : Array U32 n) :
    core.array.equality.PartialEqArray.eq AspisR1TerminalDecoder.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a b = ok (decide (a=b)) := by
  unfold core.array.equality.PartialEqArray.eq
  have length : a.length=b.length := by have := a.property; have := b.property; scalar_tac
  rw [if_pos length, list_eq a.val b.val (by have := a.property; have := b.property; scalar_tac)]
  have eqv : (a.val=b.val) ↔ a=b := by
    cases a
    cases b
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl
  simp only [eqv]

#print axioms list_eq
#print axioms source
end NBN_WordArrayEq
