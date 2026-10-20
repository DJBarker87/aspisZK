import AspisR1FastDotsCurrent.FunsOpsV4
import Aeneas.Std.RangeIter
import StepByScheduleV3
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsBatchBodyAdvance
abbrev Range := core.ops.range.Range Usize
abbrev StepBy := core.iter.adapters.step_by.StepBy Range
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
/-- A successful continuation of the actual emitted outer batch body must have
    obtained its batch cursor from `StepBy.next`; the retained Aeneas spec gives
    the exact saturated cursor transition. Inner arithmetic remains untouched. -/
theorem body_success_cont_step (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (a : Array U8 608#usize) (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter it' : StepBy) (limbs limbs' : Array U64 8#usize)
    (hstepEq0 : iter.step_by = 4#usize)
    (hbody : AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
      ops a a1 slot iter limbs = .ok (.cont (it', limbs'))) :
    ∃ start,
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (some start, it') ∧
      start = iter.iter.start ∧
      it'.iter.start.val = min (iter.iter.start.val + iter.step_by.val) iter.iter.end.val ∧
      it'.iter.end = iter.iter.end ∧ it'.step_by = iter.step_by := by
  unfold AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  have hstep : iter.step_by.val > 0 := by rw [hstepEq0]; simp
  have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hstep
  cases o with
  | none =>
      simp only [bind_tc_ok] at hrest
      cases Result.ok.inj hrest
  | some start =>
      rw [hnext, WP.spec_ok] at hspec
      by_cases hstart : iter.iter.start.val < iter.iter.end.val
      · simp only [hstart, ↓reduceIte] at hspec
        rcases hspec with ⟨⟨hstartEq, hcursor⟩, hend, hstepEq⟩
        cases Option.some.inj hstartEq
        simp only [bind_tc_ok] at hrest
        obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨limbsFinal, _, hrest⟩ := bind_success _ _ _ hrest
        have hp := Result.ok.inj hrest
        have hiter : iter1 = it' := congrArg Prod.fst (ControlFlow.cont.inj hp)
        subst it'
        exact ⟨iter.iter.start, by simpa using hnext, rfl, hcursor, hend, hstepEq⟩
      · simp only [hstart, ↓reduceIte] at hspec
        rcases hspec with ⟨⟨hnone, _⟩, _, _⟩
        cases hnone
#print axioms body_success_cont_step
end AspisR1FastDotsBatchBodyAdvance
