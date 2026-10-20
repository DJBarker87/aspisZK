import AspisR1FastDotsCurrent.FunsOpsV4
import FourDotsBatchBodyAdvanceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsBatchInnerCalls
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
/-- Expose the actual successful calls made by one emitted outer batch body.
    This records the source-selected term range, its successful term loop, the
    actual wide-limb count call, and the successful limb-reduction loop. -/
theorem body_success_cont_inner_calls
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (a : Array U8 608#usize)
    (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter it' : AspisR1FastDotsBatchBodyAdvance.StepBy)
    (limbs limbs' : Array U64 8#usize)
    (hbody : AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
      ops a a1 slot iter limbs = .ok (.cont (it', limbs'))) :
    ∃ start batchEndArg rangeEnd sums1 limbCount,
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (some start, it') ∧
      UScalar.add start 4#usize = .ok batchEndArg ∧
      core.cmp.min core.cmp.OrdUsize batchEndArg 26#usize = .ok rangeEnd ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
        ops { start, «end» := rangeEnd } a a1 slot (Array.repeat 8#usize 0#u64) = .ok sums1 ∧
      ops.wideLimbCount = .ok limbCount ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
        ops { start := 0#usize, «end» := limbCount } limbs sums1 = .ok limbs' := by
  unfold AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => simp only [bind_tc_ok] at hrest; cases Result.ok.inj hrest
  | some start =>
      simp only [bind_tc_ok] at hrest
      obtain ⟨batchEndArg, hadd, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨rangeEnd, hmin, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨sums1, hterms, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨limbCount, hcount, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨limbsFinal, hlimbs, hrest⟩ := bind_success _ _ _ hrest
      have hp := Result.ok.inj hrest
      have hpair : (iter1, limbsFinal) = (it', limbs') := ControlFlow.cont.inj hp
      rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
      exact ⟨start, batchEndArg, rangeEnd, sums1, limbCount, hnext, hadd, hmin, hterms, hcount, hlimbs⟩
#print axioms body_success_cont_inner_calls
end AspisR1FastDotsBatchInnerCalls
