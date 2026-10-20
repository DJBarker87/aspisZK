import FourDotsActualTermLoopLinearBoundV1
import FourDotsBatchInnerCallsV1
import FourDotsBatchRangeBoundV4
import FourDotsBatchBodyAdvanceV1
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualBatchTermsAndLimbCallsV2

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy
abbrev BatchBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
abbrev TermLoop := AspisR1FastDotsActualTermLoopLinearBoundV1.TermLoop
abbrev cap := AspisR1FastDotsActualTermLoopLinearBoundV1.cap
abbrev cell := AspisR1FastDotsActualTermLoopLinearBoundV1.cell
abbrev Range := core.ops.range.Range Usize

/-- The actual emitted batch body determines its selected four-term range,
    bounded term sums, concrete limb-count call, and exact limb-loop result. -/
theorem current_batch_terms_and_limb_calls
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (iter it' : StepBy)
    (limbs limbs' : Array U64 8#usize)
    (houterEnd : iter.iter.end.val = 26)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (hstepEq0 : iter.step_by = 4#usize)
    (hbody : BatchBody
      (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
      a a1 slot iter limbs = .ok (.cont (it', limbs'))) :
    ∃ start batchEndArg rangeEnd sums1 limbCount,
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (some start, it') ∧
      UScalar.add start 4#usize = .ok batchEndArg ∧
      core.cmp.min core.cmp.OrdUsize batchEndArg 26#usize = .ok rangeEnd ∧
      TermLoop (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
        { start, «end» := rangeEnd } a a1 slot (Array.repeat 8#usize 0#u64) = .ok sums1 ∧
      (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops).wideLimbCount =
        .ok limbCount ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1
        (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
        { start := 0#usize, «end» := limbCount } limbs sums1 = .ok limbs' ∧
      (∀ i : Fin 8, cell sums1 i ≤ 4 * cap) := by
  obtain ⟨start, hnext, hstart, _, _, _⟩ :=
    AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
      (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
      a a1 slot iter it' limbs limbs' hstepEq0 hbody
  obtain ⟨start', batchEndArg, rangeEnd, sums1, limbCount, hnext', hadd, hmin,
      hterms, hcount, hlimbs⟩ :=
    AspisR1FastDotsBatchInnerCalls.body_success_cont_inner_calls
      (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
      a a1 slot iter it' limbs limbs' hbody
  have hstartEq : start' = start := by
    have hpair := Result.ok.inj (hnext.symm.trans hnext')
    exact (Option.some.inj (congrArg Prod.fst hpair)).symm
  have hstartBound : start'.val < 26 := by
    have : start = iter.iter.start := hstart
    have hstepPositive : iter.step_by.val > 0 := by rw [hstepEq0]; simp
    have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec
      iter hstepPositive
    rw [hnext, WP.spec_ok] at hspec
    by_cases hlt : iter.iter.start.val < iter.iter.end.val
    · rw [hstartEq, this, ← houterEnd]
      exact hlt
    · simp only [hlt, ↓reduceIte] at hspec
      rcases hspec with ⟨⟨hnone, _⟩, _, _⟩
      cases hnone
  have hwidth := AspisR1FastDotsBatchRangeBound.width_le_four
    start' batchEndArg rangeEnd hstartBound hadd hmin
  have hzero : ∀ i : Fin 8,
      cell (Array.repeat 8#usize 0#u64) i ≤ 0 := by
    intro i
    fin_cases i <;> rfl
  have hbudget : 0 + 4 ≤ 4 := by omega
  have htermBound := AspisR1FastDotsActualTermLoopLinearBoundV1.term_loop_success_linear_bound
    (ops := ops) (k := 0) (a := a) (a1 := a1) (slot := slot)
    (iter := { start := start', «end» := rangeEnd })
    (sums := Array.repeat 8#usize 0#u64) (out := sums1) (d := 4)
    hcoords hzero hwidth hbudget hterms
  exact ⟨start', batchEndArg, rangeEnd, sums1, limbCount,
    hnext', hadd, hmin, hterms, hcount, hlimbs, htermBound⟩

#print axioms current_batch_terms_and_limb_calls

end AspisR1FastDotsActualBatchTermsAndLimbCallsV2
