import FourDotsActualTermTraceBoundsRootV1
import FourDotsActualBatchTermsAndLimbCallsV2
import S4BatchAccumulatorExactV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualBatchExactRootV1
open AspisR1FastDotsActualTermTraceRootV1
abbrev U8 := Std.U8
abbrev U64 := Std.U64
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy
abbrev BatchBody := AspisR1FastDotsActualBatchTermsAndLimbCallsV2.BatchBody
abbrev actualOps := AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps

/-- A successful actual batch supplies the same bounded parsed contribution
list to its term sum and fold-loop update. -/
theorem current_batch_body_success_exact
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (iter it' : StepBy) (limbs limbs' : Array U64 8#usize)
    (houterEnd : iter.iter.end.val = 26)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (hstep : iter.step_by = 4#usize)
    (hbody : BatchBody (actualOps ops) a a1 slot iter limbs = .ok (.cont (it',limbs'))) :
    ∃ (start batchEndArg rangeEnd : Usize) (sums : Array U64 8#usize)
      (cs : List Contribution),
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (some start,it') ∧
      UScalar.add start 4#usize = .ok batchEndArg ∧
      core.cmp.min core.cmp.OrdUsize batchEndArg 26#usize = .ok rangeEnd ∧
      TermLoop (actualOps ops) {start, «end» := rangeEnd} a a1 slot
        (Array.repeat 8#usize 0#u64) = .ok sums ∧
      ActualTermTrace (actualOps ops) a a1 slot {start, «end» := rangeEnd}
        (Array.repeat 8#usize 0#u64) sums cs ∧
      cs.length ≤ 4 ∧
      (∀ c ∈ cs, ∀ j : Fin 8, c.product j ≤ cap) ∧
      ∀ j : Fin 8, cell limbs' j = cell limbs j +
        AspisR1BatchedFoldSourceStep.fold ((cs.map (fun c => c.product j)).sum) := by
  obtain ⟨start,batchEndArg,rangeEnd,sums,limbCount,hnext,hadd,hmin,hterms,hcount,hfold,hbound⟩ :=
    AspisR1FastDotsActualBatchTermsAndLimbCallsV2.current_batch_terms_and_limb_calls
      ops a a1 slot iter it' limbs limbs' houterEnd hcoords hstep hbody
  have hstartBound : start.val < 26 := by
    have hpos : iter.step_by.val > 0 := by rw [hstep]; decide
    have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hpos
    rw [hnext,WP.spec_ok] at hspec
    by_cases hlt : iter.iter.start.val < iter.iter.end.val
    · simp only [hlt,↓reduceIte] at hspec
      rcases hspec with ⟨⟨hsome,hcursor⟩,hend,hstep'⟩
      have hs : start = iter.iter.start := Option.some.inj hsome
      rw [hs,←houterEnd]
      exact hlt
    · simp only [hlt,↓reduceIte] at hspec
      rcases hspec with ⟨⟨hnone,_⟩,_,_⟩
      cases hnone
  have hwidth := AspisR1FastDotsBatchRangeBound.width_le_four
    start batchEndArg rangeEnd hstartBound hadd hmin
  have hzero : ∀ j : Fin 8, cell (Array.repeat 8#usize 0#u64) j = 0 := by
    intro j
    fin_cases j <;> rfl
  have hinput : ∀ j : Fin 8, cell (Array.repeat 8#usize 0#u64) j ≤ 0*cap := by
    intro j
    rw [hzero j,Nat.zero_mul]
  obtain ⟨cs,htrace,hlen,hsums⟩ := actual_term_loop_success_trace
    ops 0 a a1 slot {start, «end» := rangeEnd}
    (Array.repeat 8#usize 0#u64) sums 4 hcoords hinput hwidth (by decide) hterms
  have hproducts := AspisR1FastDotsActualTermTraceBoundsRootV1.actual_trace_products_bounded
    (actualOps ops) a a1 slot {start, «end» := rangeEnd}
    (Array.repeat 8#usize 0#u64) sums cs hcoords htrace
  have hcount8 : limbCount = 8#usize := Result.ok.inj
    (hcount.symm.trans (show (actualOps ops).wideLimbCount = .ok 8#usize from rfl))
  rw [hcount8] at hfold
  have hfoldValues := AspisR1FromFnP6GeneratedV2.actual_loop0_loop1_success_exact_batch_values
    (actualOps ops) sums limbs limbs' hfold
  refine ⟨start,batchEndArg,rangeEnd,sums,cs,hnext,hadd,hmin,hterms,htrace,hlen,hproducts,?_⟩
  intro j
  have hs : cell sums j = (cs.map (fun c => c.product j)).sum := by
    simpa only [hzero j,Nat.zero_add] using hsums j
  have hv : cell limbs' j = cell limbs j + AspisR1BatchedFoldSourceStep.fold (cell sums j) :=
    hfoldValues j
  rw [hs] at hv
  exact hv
#print axioms current_batch_body_success_exact
end AspisR1FastDotsActualBatchExactRootV1
