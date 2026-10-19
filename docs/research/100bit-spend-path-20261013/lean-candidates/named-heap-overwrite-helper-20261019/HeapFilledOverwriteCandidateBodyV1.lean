import AspisR1HeapFilledOverwrite.Funs
import OccupancyRangeTraversal
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1HeapFilledOverwrite

namespace HeapFilledOverwriteCandidateBodyV1

abbrev Iter := core.ops.range.Range Std.Usize
abbrev Raw (T : Type) := alloc.vec.Vec T

private theorem bind_ok_inv {α β : Type} (r : Result α) (f : α → Result β) (y : β)
    (h : (do let x ← r; f x) = .ok y) : ∃ x, r = .ok x ∧ f x = .ok y := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem body_cont_update {T : Type} (value : T) (iter : Iter)
    (raw : Raw T) (iterOut : Iter) (rawOut : Raw T)
    (h : aspis_core.r0.heap.filled_overwrite_loop.body value iter raw =
      .ok (.cont (iterOut, rawOut))) :
    iterOut.start.val = iter.start.val + 1 ∧
      iterOut.end = iter.end ∧
      rawOut = alloc.vec.Vec.set raw iter.start value := by
  change (do
      let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok (done raw)
      | some index => do
          let (_, back) ← alloc.vec.Vec.index_mut
            (core.slice.index.SliceIndexUsizeSlice T) raw index
          let out1 := back value
          ok (cont (iter1, out1))) = .ok (.cont (iterOut, rawOut)) at h
  have hlt : iter.start.val < iter.end.val := by
    by_contra hn
    have hstop := AspisR1.OccupancyRangeTraversal.next_done iter (Nat.le_of_not_gt hn)
    simp only [hstop, bind_tc_ok] at h
    cases h
  obtain ⟨iter1, hnext, hstart, hend, _⟩ :=
    AspisR1.OccupancyRangeTraversal.next_step iter hlt
  let next := core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  let after := fun p : Option Std.Usize × Iter =>
    match p.1 with
    | none => ok (done raw)
    | some index => do
        let (_, back) ← alloc.vec.Vec.index_mut
          (core.slice.index.SliceIndexUsizeSlice T) raw index
        let out1 := back value
        ok (cont (p.2, out1))
  obtain ⟨p, hp, hafter⟩ := bind_ok_inv next after (.cont (iterOut, rawOut)) h
  have hp' : p = (some iter.start, iter1) := by
    have hh := hp
    change core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok p at hh
    rw [hnext] at hh
    injection hh with hp
    exact hp.symm
  subst p
  simp only [after] at hafter
  obtain ⟨pair, hmut, hfinal⟩ := bind_ok_inv
    (alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice T) raw iter.start)
    (fun pair => let (_, back) := pair; ok (cont (iter1, back value)))
    (.cont (iterOut, rawOut)) hafter
  have hiter : iterOut = iter1 := by
    injection hfinal with hcf
    injection hcf with hpair
    exact (congrArg Prod.fst hpair).symm
  rcases pair with ⟨old, back⟩
  have hout : back value = rawOut := by
    injection hfinal with hcf
    injection hcf with hpair
    exact congrArg Prod.snd hpair
  have hback : back = alloc.vec.Vec.set raw iter.start := by
    simp only [alloc.vec.Vec.index_mut,
      core.slice.index.SliceIndexUsizeSlice,
      core.slice.index.Usize.index_mut, Slice.index_mut_usize] at hmut
    cases hr : Slice.index_usize (raw : Slice T) iter.start with
    | fail e => simp [hr] at hmut
    | div => simp [hr] at hmut
    | ok oldRead =>
        simp only [hr, bind_tc_ok] at hmut
        have hp : (oldRead, Slice.set raw iter.start) = (old, back) := by
          injection hmut
        change back = Slice.set raw iter.start
        exact (congrArg Prod.snd hp).symm
  constructor
  · rw [hiter, hstart]
  · constructor
    · rw [hiter, hend]
    · rw [← hout, hback]

#print axioms body_cont_update
end HeapFilledOverwriteCandidateBodyV1
