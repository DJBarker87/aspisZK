import AspisR1FastDotsCurrent.FunsOpsV4
import Aeneas.Std.RangeIter
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsBatchBodyDone
abbrev Range := core.ops.range.Range Usize
abbrev StepBy := core.iter.adapters.step_by.StepBy Range
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
/-- A successful terminal result from the real outer-body definition means its
    step-by iterator was already exhausted; a batch is never silently omitted. -/
theorem body_success_done_exhausted (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (a : Array U8 608#usize) (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter : StepBy) (limbs limbs' : Array U64 8#usize)
    (hstepEq0 : iter.step_by = 4#usize)
    (hbody : AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
      ops a a1 slot iter limbs = .ok (.done limbs')) :
    iter.iter.start.val ≥ iter.iter.end.val := by
  unfold AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  have hstep : iter.step_by.val > 0 := by rw [hstepEq0]; simp
  have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hstep
  cases o with
  | none =>
      by_contra hn
      have hlt : iter.iter.start.val < iter.iter.end.val := by omega
      rw [hnext, WP.spec_ok] at hspec
      simp only [hlt, ↓reduceIte] at hspec
      rcases hspec with ⟨⟨hopt', _⟩, _, _⟩
      simp at hopt'
  | some start =>
      simp only [bind_tc_ok] at hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨limbsFinal, _, hrest⟩ := bind_success _ _ _ hrest
      have hp := Result.ok.inj hrest
      cases hp
#print axioms body_success_done_exhausted
end AspisR1FastDotsBatchBodyDone
