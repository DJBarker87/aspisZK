import FourDotsBatchActualRangeV2
import FourDotsBatchBodyDoneV1
import FourDotsBatchLoopScheduleV1
import FourDotsBatchExactSevenV1
import StepByScheduleV3
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsBatchWorkTrace
open AspisR1FastDotsBatchLoopSchedule

inductive WorkTrace (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (a : Array U8 608#usize)
    (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) : StepBy → List Nat → Prop where
  | stop (it : StepBy) (hstop : it.iter.start.val ≥ it.iter.end.val) :
      WorkTrace ops a a1 slot it []
  | step {it it' : StepBy} {tail : List Nat}
      (hstart : it.iter.start.val < it.iter.end.val)
      (hcursor : it'.iter.start.val = min (it.iter.start.val + it.step_by.val) it.iter.end.val)
      (hend : it'.iter.end = it.iter.end)
      (hstep : it'.step_by = it.step_by)
      (hwork : ∃ rangeEnd sums1,
        rangeEnd.val - it.iter.start.val ≤ 4 ∧
        AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
          ops { start := it.iter.start, «end» := rangeEnd } a a1 slot
          (Array.repeat 8#usize 0#u64) = .ok sums1)
      (htail : WorkTrace ops a a1 slot it' tail) :
      WorkTrace ops a a1 slot it (it.iter.start.val :: tail)

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem outer_loop_equation (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (iter : StepBy) (a : Array U8 608#usize)
    (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (limbs : Array U64 8#usize) :
    Outer ops iter a a1 slot limbs =
      match Body ops a a1 slot iter limbs with
      | .ok (.cont (iter1, limbs1)) => Outer ops iter1 a a1 slot limbs1
      | .ok (.done out) => ok out
      | .fail e => .fail e
      | .div => .div := by
  change AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
    ops iter a a1 slot limbs = _
  conv_lhs => unfold AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0; rw [loop]
  cases hb : Body ops a a1 slot iter limbs with
  | fail e => simp only [hb, bind_tc_fail]
  | div => simp only [hb, bind_tc_div]
  | ok flow =>
      cases flow with
      | done out => simp only [hb, bind_tc_ok]
      | cont pair => simp only [hb, bind_tc_ok]; cases pair with | mk iter1 limbs1 => rfl

private theorem forget_work {ops : AspisR1FastDotsCurrent.FourDotsOps}
    {a : Array U8 608#usize}
    {a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize}
    {slot : Usize} {it : StepBy} {starts : List Nat}
    (h : WorkTrace ops a a1 slot it starts) : BatchTrace it starts := by
  induction h with
  | stop it hstop => exact .stop it hstop
  | @step it it' tail hstart hcursor hend hstep hwork htail ih =>
      exact .step hstart hcursor hend hstep ih

/-- Successful execution of the actual emitted outer loop retains, at every
    continuing edge, the actual term-loop success and its four-wide bound. -/
theorem outer_success_work_trace
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (iter : StepBy) (a : Array U8 608#usize)
    (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (limbs : Array U64 8#usize) (out : Array U64 8#usize)
    (hend0 : iter.iter.end.val = 26)
    (hstep0 : iter.step_by = 4#usize)
    (h : Outer ops iter a a1 slot limbs = .ok out) :
    ∃ starts, WorkTrace ops a a1 slot iter starts := by
  induction hmeasure : iter.iter.end.val - iter.iter.start.val
      using Nat.strong_induction_on generalizing iter limbs with
  | h m ih =>
      change Outer ops iter a a1 slot limbs = .ok out at h
      rw [outer_loop_equation] at h
      cases hbody : Body ops a a1 slot iter limbs with
      | fail e => simp only [hbody, bind_tc_fail] at h; cases h
      | div => simp only [hbody, bind_tc_div] at h; cases h
      | ok flow =>
          cases flow with
          | done out0 =>
              simp only [hbody, bind_tc_ok] at h
              have hstop := AspisR1FastDotsBatchBodyDone.body_success_done_exhausted
                ops a a1 slot iter limbs out0 hstep0 hbody
              exact ⟨[], .stop iter hstop⟩
          | cont pair =>
              rcases pair with ⟨iter1, limbs1⟩
              simp only [hbody, bind_tc_ok] at h
              obtain ⟨start, hnext, hstartEq, hcursor, hend, hstep⟩ :=
                AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
                  ops a a1 slot iter iter1 limbs limbs1 hstep0 hbody
              have hlt : iter.iter.start.val < iter.iter.end.val := by
                have hpos : iter.step_by.val > 0 := by rw [hstep0]; simp
                have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hpos
                rw [hnext, WP.spec_ok] at hspec
                by_contra hnot
                simp only [hnot, ↓reduceIte] at hspec
                rcases hspec with ⟨⟨hnone, _⟩, _, _⟩
                cases hnone
              have hpositive : iter.step_by.val > 0 := by rw [hstep0]; simp
              have hdecrease : iter.iter.end.val - iter1.iter.start.val < m := by
                rw [hcursor]
                by_cases hmin : iter.iter.start.val + iter.step_by.val ≤ iter.iter.end.val
                · rw [Nat.min_eq_left hmin]
                  omega
                · have hle : iter.iter.end.val ≤ iter.iter.start.val + iter.step_by.val := by omega
                  rw [Nat.min_eq_right hle]
                  omega
              have hwork := AspisR1FastDotsBatchActualRange.body_success_term_range_width
                ops a a1 slot iter iter1 limbs limbs1 hend0 hstep0 hbody
              have hend1 : iter1.iter.end.val = 26 := by rw [hend]; exact hend0
              have hstep1 : iter1.step_by = 4#usize := by rw [hstep]; exact hstep0
              have hmeasure1 : iter1.iter.end.val - iter1.iter.start.val =
                  iter.iter.end.val - iter1.iter.start.val := by rw [hend]
              obtain ⟨tail, htail⟩ := ih _ hdecrease iter1 limbs1 hend1 hstep1 h hmeasure1
              exact ⟨iter.iter.start.val :: tail,
                .step hlt hcursor hend hstep hwork htail⟩

/-- The actual initialized four_dots call has seven work items, each tied to
    its concrete successful term-loop invocation and bounded selected range. -/
theorem actual_outer_seven_bounded_work
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (a : Array U8 608#usize)
    (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (limbs out : Array U64 8#usize)
    (h : Outer ops AspisR1FastDotsStepSchedule.startBy a a1 slot limbs = .ok out) :
    ∃ starts, WorkTrace ops a a1 slot AspisR1FastDotsStepSchedule.startBy starts ∧
      starts.length = 7 := by
  obtain ⟨starts, hwork⟩ := outer_success_work_trace ops AspisR1FastDotsStepSchedule.startBy
    a a1 slot limbs out (by norm_num [AspisR1FastDotsStepSchedule.startBy,
      AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy]) h
  have htrace := forget_work hwork
  have hshape := AspisR1FastDotsBatchExactSeven.trace_shape_from 7 0
    AspisR1FastDotsStepSchedule.startBy starts rfl (by omega)
    (by norm_num [AspisR1FastDotsStepSchedule.startBy,
      AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy,
      AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy]) htrace
  refine ⟨starts, hwork, ?_⟩
  rw [hshape]
  rfl

#print axioms outer_success_work_trace
#print axioms actual_outer_seven_bounded_work
end AspisR1FastDotsBatchWorkTrace
