import PV_B1_PowersOriginal
import PV_B1_Loop
set_option autoImplicit false
noncomputable section
namespace PV_B1_PowersOriginalControl
open Aeneas Aeneas.Std Result ControlFlow PV_B1_PowersOriginal
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Src {N : Usize} := PV_B1_PowersOriginal.weights.powers_loop (N := N)
abbrev Ret (N : Usize) := Array W N × Option (Array W N)
def dispatch {N : Usize} (recur : Array W N → W → Usize → Result (Ret N))
    (x : W) (out : Array W N) (p : W) (i : Usize) : Result (Ret N) := do
  if i < N then
    let (_,back) ← Array.index_mut_usize out i
    let i1 := Usize.wrapping_add i 1#usize
    if i1 = N then
      let out1 := back p
      ok (out1,some out1)
    else
      let p1 ← aspis_core.field.wide_exact.WideExact.mul p x
      recur (back p) p1 i1
  else ok (out,none)

theorem source_unfold {N : Usize} (x : W) (out : Array W N) (p : W) (i : Usize) :
    Src x out p i = dispatch (Src x) x out p i := by
  unfold Src PV_B1_PowersOriginal.weights.powers_loop
  rw [PV_B1_Loop.bind]
  unfold PV_B1_PowersOriginal.weights.powers_loop.body dispatch
  dsimp only
  by_cases h : i<N
  · simp only [h,if_true,lift,bind_tc_ok]
    cases hr : Array.index_mut_usize out i with
    | fail e => simp only [hr,bind_tc_fail]
    | div => simp only [hr,bind_tc_div]
    | ok pair =>
      rcases pair with ⟨old,back⟩
      simp only [hr,bind_tc_ok]
      try dsimp only
      by_cases last : Usize.wrapping_add i 1#usize = N
      · simp only [last,if_true,bind_tc_ok] <;> rfl
      · simp only [last,if_false]
        cases hm : aspis_core.field.wide_exact.WideExact.mul p x <;>
          simp only [hm,bind_tc_ok,bind_tc_fail,bind_tc_div] <;> rfl
  · simp only [h,if_false,bind_tc_ok]

theorem dispatch_congr {N : Usize} (x : W) (out : Array W N) (p : W) (i : Usize)
    (left right : Array W N → W → Usize → Result (Ret N))
    (same : ∀ a b, left a b (Usize.wrapping_add i 1#usize) =
      right a b (Usize.wrapping_add i 1#usize)) :
    dispatch left x out p i = dispatch right x out p i := by
  unfold dispatch
  split
  · apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro a ha
    rcases a with ⟨old,back⟩
    try dsimp only
    split
    · rfl
    · apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro b hb
      apply same
  · rfl
#print axioms source_unfold
#print axioms dispatch_congr
end PV_B1_PowersOriginalControl
