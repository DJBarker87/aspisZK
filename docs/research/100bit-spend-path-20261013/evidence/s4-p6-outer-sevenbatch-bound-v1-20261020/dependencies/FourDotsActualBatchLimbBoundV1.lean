import FourDotsActualBatchTermsAndLimbCallsV2
import FourDotsActualLimbFoldBodyFacadeV2
import FourDotsActualTermBodyLinearBoundV1
import FourDotsActualEightLimbCallV1
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualBatchLimbBoundV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Range := core.ops.range.Range Usize
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy
abbrev BatchBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
abbrev BatchTermsOps := AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps
abbrev limbCap := AspisR1FastDotsActualLimbFoldBodyFacadeV2.limbCap
abbrev cell := AspisR1FastDotsActualLimbFoldBodyFacadeV2.cell

/-- One actual emitted batch body composes the source-bound four-term sums
    with its successful eight-limb reducer loop.  The initial accumulator is
    bounded by `batchCount` completed batches; the output is bounded by one
    additional limb cap. -/
theorem batch_body_success_limb_bound
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (iter it' : StepBy)
    (limbs limbs' : Array U64 8#usize) (batchCount : Nat)
    (houterEnd : iter.iter.end.val = 26)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (hstep : iter.step_by = 4#usize)
    (hinput : ∀ i : Fin 8, cell limbs i ≤ batchCount * limbCap)
    (hbody : BatchBody (BatchTermsOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
      a a1 slot iter limbs = .ok (.cont (it', limbs'))) :
    ∀ i : Fin 8, cell limbs' i ≤ (batchCount + 1) * limbCap := by
  obtain ⟨_start, _batchEndArg, _rangeEnd, sums, limbCount,
      _hnext, _hadd, _hmin, hterms, hcount, hlimbs, hsums⟩ :=
    AspisR1FastDotsActualBatchTermsAndLimbCallsV2.current_batch_terms_and_limb_calls
      (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)
      a a1 slot iter it' limbs limbs' houterEnd hcoords hstep hbody
  have hcount8 : limbCount = 8#usize := by
    have hc : (BatchTermsOps
      (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)).wideLimbCount =
        .ok limbCount := hcount
    have hc' : Result.ok 8#usize = Result.ok limbCount := by
      change Result.ok 8#usize = Result.ok limbCount
      exact hc
    exact (Result.ok.inj hc').symm
  subst limbCount
  have hsums' : ∀ i : Fin 8, cell sums i ≤ 4 *
      AspisR1FastDotsActualLimbFoldBodyFacadeV2.productCap := by
    intro i
    have hcap : AspisR1FastDotsActualBatchTermsAndLimbCallsV2.cap =
        AspisR1FastDotsActualLimbFoldBodyFacadeV2.productCap := by
      norm_num [AspisR1FastDotsActualBatchTermsAndLimbCallsV2.cap,
        AspisR1FastDotsActualTermLoopLinearBoundV1.cap,
        AspisR1FastDotsActualInnerLoopLinearBoundV1.cap,
        AspisR1FastDotsActualLimbFoldBodyFacadeV2.productCap]
    have hsum := hsums i
    rw [hcap] at hsum
    simpa only [AspisR1FastDotsActualBatchTermsAndLimbCallsV2.cell,
      AspisR1FastDotsActualTermLoopLinearBoundV1.cell,
      AspisR1FastDotsActualInnerLoopLinearBoundV1.cell,
      AspisR1FastDotsActualLimbFoldBodyFacadeV2.cell] using hsum
  have hout := AspisR1FastDotsActualLimbFoldBodyFacadeV2.limb_loop_generated_call_batch_bound
    (BatchTermsOps (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))
    sums { start := 0#usize, «end» := 8#usize } limbs limbs' batchCount
    hsums' hinput hlimbs
  exact hout

#print axioms batch_body_success_limb_bound

end AspisR1FastDotsActualBatchLimbBoundV1
