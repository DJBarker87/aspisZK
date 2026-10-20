import V6BatchLimbBoundBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsV6OuterBatchBoundBridgeV1

abbrev Ops := AspisR1FastDotsActualBatchLimbBoundV1.Ops
abbrev Usize := Std.Usize
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsActualBatchLimbBoundV1.Wide
abbrev StepBy := AspisR1FastDotsActualBatchLimbBoundV1.StepBy
abbrev NewBody := AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0.body
abbrev OldBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem old_body_none_success
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs : Array U64 8#usize)
    (iter1 : StepBy)
    (hnext : core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
        .ok (none, iter1)) :
    OldBody
      (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps
        (AspisR1FastDotsActualBatchLimbBoundV1.BatchTermsOps
          (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)))
      q g slot iter limbs = .ok (.done limbs) := by
  change AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
      (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps
        (AspisR1FastDotsActualBatchLimbBoundV1.BatchTermsOps
          (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)))
      q g slot iter limbs = .ok (.done limbs)
  unfold AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
  rw [hnext]
  rfl


theorem new_body_done_next_none
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs : Array U64 8#usize) (out : Array U64 8#usize)
    (hbody : NewBody
      (AspisR1FastDotsActualBatchLimbBoundV1.BatchTermsOps
        (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
      q g slot iter limbs = .ok (.done out)) :
    ∃ iter1, core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
        .ok (none, iter1) ∧ out = limbs := by
  unfold NewBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      change Result.ok (ControlFlow.done limbs) = Result.ok (ControlFlow.done out) at hrest
      exact ⟨iter1, hnext, (ControlFlow.done.inj (Result.ok.inj hrest)).symm⟩
  | some start =>
      repeat' (obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest)
      cases hrest

#print axioms old_body_none_success


theorem new_body_success_old_body
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs : Array U64 8#usize)
    (flow : ControlFlow (StepBy × Array U64 8#usize) (Array U64 8#usize))
    (hcount : (AspisR1FastDotsActualBatchLimbBoundV1.BatchTermsOps
      (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)).wideLimbCount = .ok 8#usize)
    (hbody : NewBody
      (AspisR1FastDotsActualBatchLimbBoundV1.BatchTermsOps
        (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
      q g slot iter limbs = .ok flow) :
    OldBody
      (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps
        (AspisR1FastDotsActualBatchLimbBoundV1.BatchTermsOps
          (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)))
      q g slot iter limbs = .ok flow := by
  cases flow with
  | cont pair =>
      rcases pair with ⟨iter', limbs'⟩
      exact AspisR1FastDotsNewOuterLimbLoopSegmentV1.fixed_batch_body_success_old_body
        (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps
          (AspisR1FastDotsActualBatchLimbBoundV1.BatchTermsOps
            (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)))
        q g slot iter iter' limbs limbs' hcount hbody
  | done out =>
      obtain ⟨iter1, hnext, hout⟩ := new_body_done_next_none ops q g slot iter limbs out hbody
      have hold := old_body_none_success ops q g slot iter limbs iter1 hnext
      rw [hout]
      exact hold

#print axioms new_body_success_old_body
end AspisR1FastDotsV6OuterBatchBoundBridgeV1
