import HeapFilledOverwriteCandidateLoopV1
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1HeapFilledOverwrite
open HeapFilledOverwriteLoopV1

namespace HeapFilledOverwriteSuccessV1

theorem resize_success_length {T : Type} (clone : core.clone.Clone T)
    (base out : alloc.vec.Vec T) (n : Std.Usize) (value : T)
    (h : alloc.vec.Vec.resize clone base n value = .ok out) :
    out.length = n.val := by
  unfold alloc.vec.Vec.resize at h
  split_ifs at h with hlt
  · injection h with hout
    subst out
    simp only [alloc.vec.Vec.length]
    change (List.resize (↑base) n.val value).length = n.val
    simp [List.resize, List.length_append, List.length_take, List.length_replicate,
      Nat.min_eq_left (Nat.le_of_lt hlt), Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
  · have hle : List.length (↑base : List T) ≤ n.val := by
      simpa only [alloc.vec.Vec.length] using (Nat.le_of_not_gt hlt)
    cases hclone : clone.clone value with
    | fail e => simp [hclone] at h
    | div => simp [hclone] at h
    | ok cloned =>
      simp only [hclone, bind_tc_ok] at h
      injection h with hout
      subst out
      simp only [alloc.vec.Vec.length]
      change (List.resize (↑base) n.val cloned).length = n.val
      simp [List.resize, List.length_append, List.length_take, List.length_replicate,
        Nat.min_eq_right hle] <;> omega

theorem filled_success_contents {T : Type} (copyInst : core.marker.Copy T)
    (n : Std.Usize) (value : T) (out : alloc.vec.Vec T)
    (h : aspis_core.r0.heap.filled_overwrite copyInst n value = .ok (.Ok out)) :
    out.length = n.val ∧
      ∀ i : Std.Usize, i.val < n.val →
        Slice.index_usize (out : Slice T) i = .ok value := by
  unfold aspis_core.r0.heap.filled_overwrite at h
  cases htry : alloc.vec.Vec.try_reserve_exact Global (alloc.vec.Vec.new T) n with
  | fail e => simp [htry] at h
  | div => simp [htry] at h
  | ok pair =>
    rcases pair with ⟨reserve, base⟩
    cases reserve with
    | Err err =>
      simp [htry, core.result.Result.map_err,
        core.result.Result.Insts.CoreOpsTry.branch,
        aspis_core.r0.heap.filled_overwrite.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
    | Ok token =>
      simp only [htry, core.result.Result.map_err, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at h
      change (do
        let resized ← alloc.vec.Vec.resize copyInst.cloneInst base n value
        let filled ← aspis_core.r0.heap.filled_overwrite_loop
          { start := 0#usize, «end» := n } value resized
        ok (core.result.Result.Ok filled)) = .ok (.Ok out) at h
      cases hresize : alloc.vec.Vec.resize copyInst.cloneInst base n value with
      | fail e => simp [hresize] at h
      | div => simp [hresize] at h
      | ok resized =>
        simp only [hresize, bind_tc_ok] at h
        cases hloop : aspis_core.r0.heap.filled_overwrite_loop
            { start := 0#usize, «end» := n } value resized with
        | fail e => simp [hloop] at h
        | div => simp [hloop] at h
        | ok filled =>
          simp only [hloop, bind_tc_ok] at h
          injection h with hres
          injection hres with hout
          subst out
          have hlen := resize_success_length copyInst.cloneInst base resized n value hresize
          have hfilled := loop_success_fill_fuel value
            { start := 0#usize, «end» := n } resized n.val
            (by simp) (by simpa using hlen)
            (by intro i hi; change i.val < 0 at hi; omega) filled hloop
          rcases hfilled with ⟨houtlen, houtvals⟩
          constructor
          · exact houtlen.trans hlen
          · intro i hi
            apply houtvals i
            simpa using hi

#print axioms filled_success_contents
end HeapFilledOverwriteSuccessV1
