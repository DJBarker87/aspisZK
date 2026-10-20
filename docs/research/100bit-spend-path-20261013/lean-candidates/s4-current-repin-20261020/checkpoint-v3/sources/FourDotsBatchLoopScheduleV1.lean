import AspisR1FastDotsCurrent.FunsOpsV4
import Aeneas.Std.RangeIter
import FourDotsBatchBodyAdvanceV1
import FourDotsBatchBodyDoneV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsBatchLoopSchedule
abbrev Range := core.ops.range.Range Usize
abbrev StepBy := core.iter.adapters.step_by.StepBy Range
abbrev Outer := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
abbrev Body := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem loop_equation (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (iter : StepBy) (a : Array U8 608#usize)
    (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (limbs : Array U64 8#usize) :
    AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0 ops iter a a1 slot limbs =
      match Body ops a a1 slot iter limbs with
      | .ok (.cont (iter1, limbs1)) => Outer ops iter1 a a1 slot limbs1
      | .ok (.done out) => ok out
      | .fail e => .fail e
      | .div => .div := by
  conv_lhs => unfold AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0; rw [loop]
  cases hb : Body ops a a1 slot iter limbs with
  | fail e => simp only [hb, bind_tc_fail]
  | div => simp only [hb, bind_tc_div]
  | ok flow =>
      cases flow with
      | done out => simp only [hb, bind_tc_ok]
      | cont pair =>
          simp only [hb, bind_tc_ok]
          cases pair with
          | mk iter1 limbs1 => rfl
inductive BatchTrace : StepBy → List Nat → Prop where
  | stop (it : StepBy) (hstop : it.iter.start.val ≥ it.iter.end.val) :
      BatchTrace it []
  | step {it it' : StepBy} {tail : List Nat}
      (hstart : it.iter.start.val < it.iter.end.val)
      (hcursor : it'.iter.start.val = min (it.iter.start.val + it.step_by.val) it.iter.end.val)
      (hend : it'.iter.end = it.iter.end)
      (hstep : it'.step_by = it.step_by)
      (htail : BatchTrace it' tail) :
      BatchTrace it (it.iter.start.val :: tail)
/-- Successful execution of the actual emitted step-by loop yields a finite
    batch trace. Each trace edge comes from the actual emitted body success;
    its stop edge is forced by the same body, not a separate schedule premise. -/
theorem outer_success_trace (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (iter : StepBy) (a : Array U8 608#usize)
    (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (limbs : Array U64 8#usize) (out : Array U64 8#usize)
    (hstep0 : iter.step_by = 4#usize)
    (h : Outer ops iter a a1 slot limbs = .ok out) :
    ∃ starts, BatchTrace iter starts := by
  induction hmeasure : iter.iter.end.val - iter.iter.start.val using Nat.strong_induction_on generalizing iter limbs with
  | h m ih =>
      change AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        ops iter a a1 slot limbs = .ok out at h
      rw [loop_equation] at h
      cases hbody : Body ops a a1 slot iter limbs with
      | fail e => simp only [hbody, bind_tc_fail] at h; cases h
      | div => simp only [hbody, bind_tc_div] at h; cases h
      | ok flow =>
          cases flow with
          | done out0 =>
              simp only [hbody, bind_tc_ok] at h
              have _hout : out0 = out := Result.ok.inj h
              have hstop := AspisR1FastDotsBatchBodyDone.body_success_done_exhausted
                ops a a1 slot iter limbs out0 hstep0 hbody
              exact ⟨[], .stop iter hstop⟩
          | cont pair =>
              rcases pair with ⟨iter1, limbs1⟩
              simp only [hbody, bind_tc_ok] at h
              obtain ⟨start, hnext, hstartEq, hcursor, hend, hstep⟩ :=
                AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
                  ops a a1 slot iter iter1 limbs limbs1 hstep0 hbody
              have hpositive : iter.step_by.val > 0 := by rw [hstep0]; simp
              have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hpositive
              rw [hnext, WP.spec_ok] at hspec
              have hlt : iter.iter.start.val < iter.iter.end.val := by
                by_contra hnot
                simp only [hnot, ↓reduceIte] at hspec
                rcases hspec with ⟨⟨hnone, _⟩, _, _⟩
                cases hnone
              simp only [hlt, ↓reduceIte] at hspec
              rcases hspec with ⟨⟨_, _⟩, _, _⟩
              have hdecrease : iter.iter.end.val - iter1.iter.start.val < m := by
                rw [hcursor]
                by_cases hmin : iter.iter.start.val + iter.step_by.val ≤ iter.iter.end.val
                · rw [Nat.min_eq_left hmin]
                  omega
                · have hle : iter.iter.end.val ≤ iter.iter.start.val + iter.step_by.val := by omega
                  rw [Nat.min_eq_right hle]
                  omega
              have hmeasure1 : iter1.iter.end.val - iter1.iter.start.val =
                  iter.iter.end.val - iter1.iter.start.val := by
                rw [hend]
              obtain ⟨tail, htail⟩ := ih _ hdecrease iter1 limbs1
                (hstep.trans hstep0) h hmeasure1
              exact ⟨iter.iter.start.val :: tail, .step hlt hcursor hend hstep htail⟩
#print axioms outer_success_trace
end AspisR1FastDotsBatchLoopSchedule
