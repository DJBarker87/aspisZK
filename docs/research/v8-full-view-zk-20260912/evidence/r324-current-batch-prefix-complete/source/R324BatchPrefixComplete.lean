import AspisV8R19.R319BatchPrefixStepExecution

/-! Bounded all-word result recurrence for both actual prefix loops.
No canonical input, prior success, nonzero or capacity premise is used.
The finite mathematical recurrence retains actual unwrap/mul/push Results. -/
set_option autoImplicit false
namespace AspisV8R19.R324BatchPrefixComplete
open Aeneas Aeneas.Std Result ControlFlow
open AspisV8R19.R319BatchPrefixStepExecution
open AspisR318BatchPrefixRaw.circle_norm.joined_inverse.line_norm.r110_norm
noncomputable section
abbrev VecU32 := alloc.vec.Vec U32

/-- Finite mathematical Result recurrence using the same executable helpers;
this is not a replacement or assumption for the extracted runtime loop. -/
def prefixResult (f : Nat → U32) : Nat → Nat → VecU32 → Result VecU32
  | _, 0, px => .ok px
  | i, n + 1, px => do
      let p ← core.option.Option.unwrap px.val.getLast?
      let b ← AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.mul p (f i)
      let px1 ← alloc.vec.Vec.push px b
      prefixResult f (i + 1) n px1

theorem batch_loop0_complete (f : Nat → U32) (n : Nat)
    (iter : PrefixIter) (px : VecU32)
    (hremaining : iter.i + n = iter.slice.val.length)
    (hread : ∀ j, iter.i ≤ j → j < iter.slice.val.length →
      iter.slice.val[j]? = some (f j)) :
    batch_loop0 iter px = prefixResult f iter.i n px := by
  induction n generalizing iter px with
  | zero =>
      have hstop : iter.slice.val.length ≤ iter.i := by omega
      rw [batch_loop0, loop.eq_def]
      dsimp only
      rw [body0_done iter px hstop]
      rfl
  | succ n ih =>
      have hstep : iter.i < iter.slice.val.length := by omega
      have hx : iter.slice.val[iter.i] = f iter.i := by
        have h := hread iter.i (by omega) hstep
        simpa only [List.getElem?_eq_getElem hstep, Option.some.injEq] using h
      let iter1 : PrefixIter := {iter with i := iter.i + 1}
      have hr : iter1.i + n = iter1.slice.val.length := by dsimp [iter1]; omega
      have hh : ∀ j, iter1.i ≤ j → j < iter1.slice.val.length →
          iter1.slice.val[j]? = some (f j) := by
        intro j hj hb
        exact hread j (by dsimp [iter1] at hj ⊢; omega) hb
      rw [batch_loop0, loop.eq_def]
      dsimp only
      rw [body0_active iter px hstep, hx]
      simp only [prefixResult]
      cases hu : core.option.Option.unwrap px.val.getLast? with
      | fail e => simp only [hu, bind_tc_fail]
      | div => simp only [hu, bind_tc_div]
      | ok p =>
        simp only [hu, bind_tc_ok]
        cases hm : AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm.B.mul p (f iter.i) with
        | fail e => simp only [hm, bind_tc_fail]
        | div => simp only [hm, bind_tc_div]
        | ok b =>
          simp only [hm, bind_tc_ok]
          cases hp : alloc.vec.Vec.push px b with
          | fail e => simp only [hp, bind_tc_fail]
          | div => simp only [hp, bind_tc_div]
          | ok px1 =>
            simp only [hp, bind_tc_ok]
            have hc := ih iter1 px1 hr hh
            simpa only [batch_loop0, iter1] using hc

theorem batch_loop1_complete (f : Nat → U32) (n : Nat)
    (iter : PrefixIter) (py : VecU32)
    (hremaining : iter.i + n = iter.slice.val.length)
    (hread : ∀ j, iter.i ≤ j → j < iter.slice.val.length →
      iter.slice.val[j]? = some (f j)) :
    batch_loop1 iter py = prefixResult f iter.i n py := by
  change batch_loop0 iter py = _
  exact batch_loop0_complete f n iter py hremaining hread

#print axioms batch_loop0_complete
#print axioms batch_loop1_complete
end
end AspisV8R19.R324BatchPrefixComplete
