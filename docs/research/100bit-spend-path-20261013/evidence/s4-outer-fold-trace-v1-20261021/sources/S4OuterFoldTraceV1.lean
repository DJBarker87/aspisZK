import FourDotsActualBatchExactRootV1
import FourDotsActualSevenBatchLimbBoundV2
import Aeneas.Std.RangeIter
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsOuterFoldTraceV1
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy
abbrev Body := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
abbrev BatchOps := AspisR1FastDotsActualSevenBatchLimbBoundV2.BatchOps
abbrev Outer := AspisR1FastDotsActualSevenBatchLimbBoundV2.Outer
abbrev Cell := AspisR1FastDotsActualSevenBatchLimbBoundV2.cell
abbrev Contribution := AspisR1FastDotsActualTermTraceRootV1.Contribution
abbrev ActualOps := AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps
abbrev LimbOps := AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8

def batchDelta (cs : List Contribution) (j : Fin 8) : Nat :=
  AspisR1BatchedFoldSourceStep.fold ((cs.map fun c => c.product j).sum)

inductive ExactTrace (ops : Ops) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) :
    StepBy → Array U64 8#usize → Array U64 8#usize →
      List (List Contribution) → List Nat → Prop where
  | stop (it : StepBy) (limbs out : Array U64 8#usize)
      (hstep4 : it.step_by = 4#usize)
      (hbody : Body (BatchOps (LimbOps ops)) a a1 slot it limbs = .ok (.done out))
      (hout : out = limbs) : ExactTrace ops a a1 slot it limbs out [] []
  | step {it it' : StepBy} {limbs limbs' out : Array U64 8#usize}
      {cs : List Contribution} {tail : List (List Contribution)} {starts : List Nat}
      (hstep4 : it.step_by = 4#usize) (hnextStep4 : it'.step_by = 4#usize)
      (hstart : it.iter.start.val < it.iter.end.val)
      (hcursor : it'.iter.start.val = min (it.iter.start.val + it.step_by.val) it.iter.end.val)
      (hend : it'.iter.end = it.iter.end)
      (hbody : Body (BatchOps (LimbOps ops)) a a1 slot it limbs = .ok (.cont (it',limbs')))
      (hdelta : ∀ j : Fin 8, Cell limbs' j = Cell limbs j + batchDelta cs j)
      (htail : ExactTrace ops a a1 slot it' limbs' out tail starts) :
      ExactTrace ops a a1 slot it limbs out (cs :: tail) (it.iter.start.val :: starts)

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) : ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem outer_equation (ops : Ops) (it : StepBy) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) (limbs : Array U64 8#usize) :
    Outer (BatchOps (LimbOps ops)) it a a1 slot limbs =
      match Body (BatchOps (LimbOps ops)) a a1 slot it limbs with
      | .ok (.cont (it',limbs')) => Outer (BatchOps (LimbOps ops)) it' a a1 slot limbs'
      | .ok (.done out) => .ok out
      | .fail e => .fail e
      | .div => .div := by
  change AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
    (BatchOps (LimbOps ops)) it a a1 slot limbs = _
  conv_lhs => unfold AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0; rw [loop]
  cases hb : Body (BatchOps (LimbOps ops)) a a1 slot it limbs with
  | fail e => simp only [hb, bind_tc_fail]
  | div => simp only [hb, bind_tc_div]
  | ok flow => cases flow with
    | done out => simp only [hb, bind_tc_ok]
    | cont pair => simp only [hb, bind_tc_ok]; cases pair with | mk it' limbs' => rfl

private theorem done_identity (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (it : StepBy) (limbs out : Array U64 8#usize)
    (hstep : it.step_by = 4#usize)
    (hbody : Body (BatchOps (LimbOps ops)) a a1 slot it limbs = .ok (.done out)) : out = limbs := by
  have _hstop := AspisR1FastDotsBatchBodyDone.body_success_done_exhausted
    (BatchOps ops) a a1 slot it limbs out hstep hbody
  unfold Body at hbody
  obtain ⟨⟨o,it1⟩,hnext,hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some _ =>
      have hpositive : it.step_by.val > 0 := by rw [hstep]; simp
      have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec it hpositive
      rw [hnext, WP.spec_ok] at hspec
      have hnot : ¬ it.iter.start.val < it.iter.end.val := by omega
      simp only [hnot,↓reduceIte] at hspec
      rcases hspec with ⟨⟨hnone,_⟩,_,_⟩
      simp at hnone

private theorem outer_success_exact_trace
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (it : StepBy) (limbs out : Array U64 8#usize)
    (hend : it.iter.end.val = 26) (hstep : it.step_by = 4#usize)
    (hcoords : ∀ i : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (houter : Outer (BatchOps (LimbOps ops)) it a a1 slot limbs = .ok out) :
    ∃ ds starts, ExactTrace ops a a1 slot it limbs out ds starts := by
  induction hmeasure : it.iter.end.val - it.iter.start.val
      using Nat.strong_induction_on generalizing it limbs with
  | h m ih =>
      rw [outer_equation] at houter
      cases hb : Body (BatchOps (LimbOps ops)) a a1 slot it limbs with
      | fail e => simp only [hb,bind_tc_fail] at houter; cases houter
      | div => simp only [hb,bind_tc_div] at houter; cases houter
      | ok flow =>
          cases flow with
          | done out0 =>
              simp only [hb,bind_tc_ok] at houter
              have heq : out0 = out := Result.ok.inj houter
              subst out
              have hid := done_identity ops a a1 slot it limbs out0 hstep hb
              exact ⟨[], [], .stop it limbs out0 hstep hb hid⟩
          | cont pair =>
              rcases pair with ⟨it',limbs'⟩
              simp only [hb,bind_tc_ok] at houter
              obtain ⟨_,hnext,_,hcursor,hend',hstep'⟩ :=
                AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
                  (BatchOps ops) a a1 slot it it' limbs limbs' hstep hb
              obtain ⟨start,batchEndArg,rangeEnd,sums,cs,_,_,_,hterms,htrace,hlen,hproducts,hdelta⟩ :=
                AspisR1FastDotsActualBatchExactRootV1.current_batch_body_success_exact
                  (LimbOps ops) a a1 slot it it' limbs limbs' hend hcoords hstep hb
              have hpos : it.step_by.val > 0 := by rw [hstep]; simp
              have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec it hpos
              rw [hnext,WP.spec_ok] at hspec
              have hlt : it.iter.start.val < it.iter.end.val := by
                by_contra hn
                simp only [hn,↓reduceIte] at hspec
                rcases hspec with ⟨⟨hnone,_⟩,_,_⟩
                cases hnone
              have hdecrease : it'.iter.end.val - it'.iter.start.val < m := by
                rw [hend',hcursor]
                by_cases hm : it.iter.start.val + it.step_by.val ≤ it.iter.end.val
                · rw [Nat.min_eq_left hm]
                  rw [hstep] at hm
                  omega
                · have hm' : it.iter.end.val ≤ it.iter.start.val + it.step_by.val := by omega
                  rw [Nat.min_eq_right hm']
                  omega
              have hendTail : it'.iter.end.val = 26 := by rw [hend']; exact hend
              have hstepNext4 : it'.step_by = 4#usize := by rw [hstep']; exact hstep
              obtain ⟨ds,starts, htail⟩ := ih _ hdecrease it' limbs' hendTail hstepNext4 houter rfl
              exact ⟨cs :: ds, it.iter.start.val :: starts,
                .step hstep hstepNext4 hlt hcursor hend' hb hdelta htail⟩

private theorem trace_cell_sum {ops : Ops} {a : Array U8 608#usize}
    {a1 : Array Wide 29#usize} {slot : Usize} {it : StepBy}
    {limbs out : Array U64 8#usize} {ds : List (List Contribution)}
    {starts : List Nat} (h : ExactTrace ops a a1 slot it limbs out ds starts) :
    ∀ j : Fin 8, Cell out j = Cell limbs j + (ds.map fun cs => batchDelta cs j).sum := by
  induction h with
  | stop it limbs out hstep4 hbody hout =>
      intro j
      simp [hout, Cell]
  | @step it it' limbs limbs' out cs tail starts hstep4 hnextStep4 hstart hcursor hend hbody hdelta htail ih =>
      intro j
      rw [ih j, hdelta j]
      simp [batchDelta, Nat.add_assoc]

private theorem trace_batch_shape {ops : Ops} {a : Array U8 608#usize}
    {a1 : Array Wide 29#usize} {slot : Usize} {it : StepBy}
    {limbs out : Array U64 8#usize} {ds : List (List Contribution)}
    {starts : List Nat} (h : ExactTrace ops a a1 slot it limbs out ds starts) :
    AspisR1FastDotsBatchLoopSchedule.BatchTrace it starts := by
  induction h with
  | stop it limbs out hstep4 hbody hout =>
      have hstop := AspisR1FastDotsBatchBodyDone.body_success_done_exhausted
        (BatchOps ops) a a1 slot it limbs out hstep4 hbody
      exact .stop it hstop
  | @step it it' limbs limbs' out cs tail starts hstep4 hnextStep4 hstart hcursor hend hbody hdelta htail ih =>
      exact .step hstart hcursor hend (hnextStep4.trans hstep4.symm) ih

private theorem trace_lengths {ops : Ops} {a : Array U8 608#usize}
    {a1 : Array Wide 29#usize} {slot : Usize} {it : StepBy}
    {limbs out : Array U64 8#usize} {ds : List (List Contribution)}
    {starts : List Nat} (h : ExactTrace ops a a1 slot it limbs out ds starts) :
    ds.length = starts.length := by
  induction h with
  | stop => rfl
  | step _ _ _ _ _ _ _ htail ih => simp [ih]

/-- The selected actual outer execution has an exact source-preserving fold
    equation for every limb. Its seven per-batch lists come from the same
    successful emitted bodies and accumulator calls. -/
theorem actual_outer_success_exact_fold_sum
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (out : Array U64 8#usize)
    (hcoords : ∀ i : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (houter : Outer (BatchOps (LimbOps ops)) AspisR1FastDotsStepSchedule.startBy a a1 slot
      (Array.repeat 8#usize 0#u64) = .ok out) :
    ∃ ds : List (List Contribution), ds.length = 7 ∧
      ∀ j : Fin 8, Cell out j = (ds.map fun cs => batchDelta cs j).sum := by
  obtain ⟨ds, starts, htrace⟩ := outer_success_exact_trace ops a a1 slot
    AspisR1FastDotsStepSchedule.startBy (Array.repeat 8#usize 0#u64) out
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy]) hcoords houter
  have hbatch := trace_batch_shape htrace
  have hshape := AspisR1FastDotsBatchExactSeven.trace_shape_from 7 0
    AspisR1FastDotsStepSchedule.startBy starts rfl (by omega)
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy, AspisR1FastDotsStepSchedule.startRange])
    (by norm_num [AspisR1FastDotsStepSchedule.startBy]) hbatch
  have hlen : starts.length = 7 := by rw [hshape]; rfl
  have hdslen := trace_lengths htrace
  have hsum := trace_cell_sum htrace
  have hzero : ∀ j : Fin 8, Cell (Array.repeat 8#usize 0#u64) j = 0 := by
    intro j
    fin_cases j <;> rfl
  refine ⟨ds, hdslen.trans hlen, ?_⟩
  intro j
  simpa [hzero j] using hsum j

#print axioms actual_outer_success_exact_fold_sum
end AspisR1FastDotsOuterFoldTraceV1
