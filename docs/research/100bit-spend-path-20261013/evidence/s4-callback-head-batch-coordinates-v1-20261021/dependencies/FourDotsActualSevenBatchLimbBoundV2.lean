import FourDotsActualBatchLimbBoundV1
import FourDotsBatchWorkTraceV4
import FourDotsBatchExactSevenV1
import FourDotsBatchBodyAdvanceV1
import FourDotsBatchBodyDoneV1
import StepByScheduleV3
import Aeneas.Std.RangeIter
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualSevenBatchLimbBoundV2

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy
abbrev Outer := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
abbrev Body := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
abbrev BatchOps := AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps
abbrev ActualBatchOps (ops : Ops) :=
  BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)
abbrev Cap := AspisR1FastDotsActualLimbFoldBodyFacadeV2.limbCap
abbrev cell := AspisR1FastDotsActualLimbFoldBodyFacadeV2.cell

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem outer_loop_equation (ops : Ops) (iter : StepBy)
    (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (limbs : Array U64 8#usize) :
    Outer ops iter a a1 slot limbs =
      match Body ops a a1 slot iter limbs with
      | .ok (.cont (iter1, limbs1)) => Outer ops iter1 a a1 slot limbs1
      | .ok (.done out) => .ok out
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

private theorem batch_body_done_identity
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs out : Array U64 8#usize)
    (hstep : iter.step_by = 4#usize)
    (hbody : Body ops a a1 slot iter limbs = .ok (.done out)) : out = limbs := by
  have _hstop := AspisR1FastDotsBatchBodyDone.body_success_done_exhausted
    ops a a1 slot iter limbs out hstep hbody
  unfold Body at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some _ =>
      have hpositive : iter.step_by.val > 0 := by rw [hstep]; simp
      have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hpositive
      rw [hnext, WP.spec_ok] at hspec
      have hnot : ¬ iter.iter.start.val < iter.iter.end.val := by omega
      simp only [hnot, ↓reduceIte] at hspec
      rcases hspec with ⟨⟨hnone, _⟩, _, _⟩
      simp at hnone

/-- A state-carrying companion to the frozen work trace.  Its `work` field
    projects to `FourDotsBatchWorkTraceV4.WorkTrace`, while each continuation
    additionally retains the exact accumulator array produced by the emitted
    body and the bound proved for that same state transition. -/
inductive BoundedWorkTrace (ops : Ops) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) :
    Nat → StepBy → Array U64 8#usize → Array U64 8#usize → List Nat → Prop where
  | stop (n : Nat) (it : StepBy) (limbs out : Array U64 8#usize)
      (hstop : it.iter.start.val ≥ it.iter.end.val) (hout : out = limbs) :
      BoundedWorkTrace ops a a1 slot n it limbs out []
  | step (n : Nat) {it it' : StepBy} {limbs limbs' out : Array U64 8#usize}
      {tail : List Nat}
      (hstart : it.iter.start.val < it.iter.end.val)
      (hcursor : it'.iter.start.val = min (it.iter.start.val + it.step_by.val) it.iter.end.val)
      (hend : it'.iter.end = it.iter.end) (hstep : it'.step_by = it.step_by)
      (hbody : Body (BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
        a a1 slot it limbs = .ok (.cont (it', limbs')))
      (hwork : ∃ rangeEnd sums1,
        rangeEnd.val - it.iter.start.val ≤ 4 ∧
        AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
          (BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
          { start := it.iter.start, «end» := rangeEnd } a a1 slot
          (Array.repeat 8#usize 0#u64) = .ok sums1)
      (hlimb : ∀ i : Fin 8, cell limbs' i ≤ (n + 1) * Cap)
      (htail : BoundedWorkTrace ops a a1 slot (n + 1) it' limbs' out tail) :
      BoundedWorkTrace ops a a1 slot n it limbs out (it.iter.start.val :: tail)

private theorem forget_bounded_work {ops : Ops} {a : Array U8 608#usize}
    {a1 : Array Wide 29#usize} {slot : Usize} {n : Nat} {it : StepBy}
    {limbs out : Array U64 8#usize} {starts : List Nat}
    (h : BoundedWorkTrace ops a a1 slot n it limbs out starts) :
    AspisR1FastDotsBatchWorkTrace.WorkTrace (ActualBatchOps ops) a a1 slot it starts := by
  induction h with
  | stop n it limbs out hstop hout => exact .stop it hstop
  | @step n it it' limbs limbs' out tail hstart hcursor hend hstep hbody hwork hlimb htail ih =>
      exact .step hstart hcursor hend hstep hwork ih

private theorem forget_bounded_to_batch {ops : Ops} {a : Array U8 608#usize}
    {a1 : Array Wide 29#usize} {slot : Usize} {n : Nat} {it : StepBy}
    {limbs out : Array U64 8#usize} {starts : List Nat}
    (h : BoundedWorkTrace ops a a1 slot n it limbs out starts) :
    AspisR1FastDotsBatchLoopSchedule.BatchTrace it starts := by
  induction h with
  | stop n it limbs out hstop hout => exact .stop it hstop
  | @step n it it' limbs limbs' out tail hstart hcursor hend hstep hbody hwork hlimb htail ih =>
      exact .step hstart hcursor hend hstep ih

private theorem work_to_batch {ops : Ops} {a : Array U8 608#usize}
    {a1 : Array Wide 29#usize} {slot : Usize} {it : StepBy} {starts : List Nat}
    (h : AspisR1FastDotsBatchWorkTrace.WorkTrace ops a a1 slot it starts) :
    AspisR1FastDotsBatchLoopSchedule.BatchTrace it starts := by
  induction h with
  | stop it hstop => exact .stop it hstop
  | @step it it' tail hstart hcursor hend hstep hwork htail ih =>
      exact .step hstart hcursor hend hstep ih

private theorem bounded_trace_output
    {ops : Ops} {a : Array U8 608#usize} {a1 : Array Wide 29#usize}
    {slot : Usize} {n : Nat} {it : StepBy} {limbs out : Array U64 8#usize}
    {starts : List Nat}
    (hinput : ∀ i : Fin 8, cell limbs i ≤ n * Cap)
    (htrace : BoundedWorkTrace ops a a1 slot n it limbs out starts) :
    ∀ i : Fin 8, cell out i ≤ (n + starts.length) * Cap := by
  induction htrace with
  | stop n it limbs out hstop hout =>
      subst out
      intro i
      simpa using hinput i
  | @step n it it' limbs limbs' out tail hstart hcursor hend hstep hbody hwork hlimb htail ih =>
      have htailBound : ∀ i : Fin 8, cell limbs' i ≤ (n + 1) * Cap := by
        simpa using hlimb
      have hout := ih htailBound
      have hcount : n + (tail.length + 1) = (n + 1) + tail.length := by omega
      rw [List.length_cons, hcount]
      exact hout

private theorem outer_success_bounded_work_trace
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt))) :
    ∀ (n : Nat) (iter : StepBy) (limbs out : Array U64 8#usize),
      iter.iter.end.val = 26 → iter.step_by = 4#usize →
      (∀ i : Fin 8, cell limbs i ≤ n * Cap) →
      Outer (BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
        iter a a1 slot limbs = .ok out →
      ∃ starts, BoundedWorkTrace ops a a1 slot n iter limbs out starts := by
  intro n iter limbs out
  induction hmeasure : iter.iter.end.val - iter.iter.start.val
      using Nat.strong_induction_on generalizing n iter limbs with
  | h m ih =>
      intro hend hstep hinput houter
      rw [outer_loop_equation] at houter
      cases hbody : Body (BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
          a a1 slot iter limbs with
      | fail e => simp only [hbody, bind_tc_fail] at houter; cases houter
      | div => simp only [hbody, bind_tc_div] at houter; cases houter
      | ok flow =>
          cases flow with
          | done out0 =>
              simp only [hbody, bind_tc_ok] at houter
              have hout : out0 = out := Result.ok.inj houter
              subst out
              have hstop : iter.iter.start.val ≥ iter.iter.end.val :=
                AspisR1FastDotsBatchBodyDone.body_success_done_exhausted
                  (BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
                  a a1 slot iter limbs out0 hstep hbody
              have hidentity : out0 = limbs := batch_body_done_identity
                (BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
                a a1 slot iter limbs out0 hstep hbody
              subst out0
              exact ⟨[], .stop n iter limbs limbs hstop rfl⟩
          | cont pair =>
              rcases pair with ⟨iter1, limbs1⟩
              simp only [hbody, bind_tc_ok] at houter
              obtain ⟨_start, _hnext, _hstart, hcursor, hend', hstep'⟩ :=
                AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
                  (BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
                  a a1 slot iter iter1 limbs limbs1 hstep hbody
              have hpositive : iter.step_by.val > 0 := by rw [hstep]; simp
              have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hpositive
              rw [_hnext, WP.spec_ok] at hspec
              have hstartlt : iter.iter.start.val < iter.iter.end.val := by
                by_contra hnot
                simp only [hnot, ↓reduceIte] at hspec
                rcases hspec with ⟨⟨hnone, _⟩, _, _⟩
                cases hnone
              have hdecrease : iter1.iter.end.val - iter1.iter.start.val < m := by
                rw [hend', hcursor]
                by_cases hmin : iter.iter.start.val + iter.step_by.val ≤ iter.iter.end.val
                · rw [Nat.min_eq_left hmin]
                  omega
                · have hle : iter.iter.end.val ≤ iter.iter.start.val + iter.step_by.val := by omega
                  rw [Nat.min_eq_right hle]
                  omega
              have hlimb := AspisR1FastDotsActualBatchLimbBoundV1.batch_body_success_limb_bound
                (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)
                a a1 slot iter iter1 limbs limbs1 n hend hcoords hstep hinput hbody
              have hend1 : iter1.iter.end.val = 26 := by rw [hend']; exact hend
              have hstep1 : iter1.step_by = 4#usize := by rw [hstep']; exact hstep
              have hwork := AspisR1FastDotsBatchActualRange.body_success_term_range_width
                (BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
                a a1 slot iter iter1 limbs limbs1 hend hstep hbody
              have hmeasure1 : iter1.iter.end.val - iter1.iter.start.val =
                  iter1.iter.end.val - iter1.iter.start.val := rfl
              obtain ⟨tail, htail⟩ := ih _ hdecrease (n + 1) iter1 limbs1
                hmeasure1 hend1 hstep1 hlimb houter
              exact ⟨iter.iter.start.val :: tail,
                .step n hstartlt hcursor hend' hstep' hbody hwork hlimb htail⟩

private theorem batch_trace_starts_unique
    {it1 it2 : StepBy} {starts1 starts2 : List Nat}
    (hstart : it1.iter.start.val = it2.iter.start.val)
    (hend : it1.iter.end.val = it2.iter.end.val)
    (hstep : it1.step_by.val = it2.step_by.val)
    (h1 : AspisR1FastDotsBatchLoopSchedule.BatchTrace it1 starts1)
    (h2 : AspisR1FastDotsBatchLoopSchedule.BatchTrace it2 starts2) : starts1 = starts2 := by
  induction h1 generalizing it2 starts2 with
  | stop it hs =>
      cases h2 with
      | stop => rfl
      | @step _ _ _ hs2 _ _ _ _ => omega
  | @step it1 it1' tail1 hs1 hc1 he1 hp1 ht1 ih =>
      cases h2 with
      | stop _ hs2 => omega
      | @step it2 it2' tail2 hs2 hc2 he2 hp2 ht2 =>
          have htailStart : it1'.iter.start.val = it2'.iter.start.val := by
            rw [hc1, hc2, hstart, hstep, hend]
          have htailEnd : it1'.iter.end.val = it2'.iter.end.val := by
            rw [he1, he2, hend]
          have htailStep : it1'.step_by.val = it2'.step_by.val := by
            rw [hp1, hp2, hstep]
          have htail := ih htailStart htailEnd htailStep ht2
          simp [hstart, htail]

/-- Actual emitted outer execution, with the exact same seven-batch schedule
    as the frozen WorkTraceV4/ExactSeven pipeline, bounds each output limb by
    seven completed reducer caps. -/
theorem actual_outer_startBy_success_seven_bound
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (out : Array U64 8#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (houter : Outer
      (BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
      AspisR1FastDotsStepSchedule.startBy a a1 slot
      (Array.repeat 8#usize 0#u64) = .ok out) :
    ∀ i : Fin 8, cell out i ≤ 7 * Cap := by
  have hzero : ∀ i : Fin 8, cell (Array.repeat 8#usize 0#u64) i ≤ 0 := by
    intro i
    fin_cases i <;> rfl
  obtain ⟨starts, hstate⟩ := outer_success_bounded_work_trace ops a a1 slot hcoords
    0 AspisR1FastDotsStepSchedule.startBy (Array.repeat 8#usize 0#u64) out
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by rfl) hzero houter
  have hstateBound := bounded_trace_output hzero hstate
  have hwork := forget_bounded_work hstate
  obtain ⟨exactStarts, hexact, hexactLen⟩ :=
    AspisR1FastDotsBatchWorkTrace.actual_outer_seven_bounded_work
      (BatchOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
      a a1 slot (Array.repeat 8#usize 0#u64) out houter
  have hbatch := work_to_batch hwork
  have hexactBatch := work_to_batch hexact
  have hsame := batch_trace_starts_unique
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by rfl) hbatch hexactBatch
  rw [hsame, hexactLen] at hstateBound
  simpa using hstateBound

#print axioms actual_outer_startBy_success_seven_bound
end AspisR1FastDotsActualSevenBatchLimbBoundV2
