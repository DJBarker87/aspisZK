import FourDotsBatchInnerCallsV1
import FourDotsBatchRangeBoundV4
import Aeneas.Std.RangeIter
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsBatchActualRange

/-- A successful emitted batch continuation passes exactly the bounded source
    range to the term reducer. The term reducer call remains an explicit
    successful result; this lemma establishes its selected range width. -/
theorem body_success_term_range_width
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (a : Array U8 608#usize)
    (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter it' : AspisR1FastDotsBatchBodyAdvance.StepBy)
    (limbs limbs' : Array U64 8#usize)
    (hend : iter.iter.end.val = 26)
    (hstep : iter.step_by = 4#usize)
    (hbody : AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
      ops a a1 slot iter limbs = .ok (.cont (it', limbs'))) :
    ∃ rangeEnd sums1,
      rangeEnd.val - iter.iter.start.val ≤ 4 ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
        ops { start := iter.iter.start, «end» := rangeEnd } a a1 slot
        (Array.repeat 8#usize 0#u64) = .ok sums1 := by
  obtain ⟨start, batchEndArg, rangeEnd, sums1, limbCount,
      hnext, hadd, hmin, hterms, hcount, hlimbs⟩ :=
    AspisR1FastDotsBatchInnerCalls.body_success_cont_inner_calls
      ops a a1 slot iter it' limbs limbs' hbody
  have hpos : iter.step_by.val > 0 := by rw [hstep]; simp
  have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hpos
  rw [hnext, WP.spec_ok] at hspec
  have hstart : iter.iter.start.val < iter.iter.end.val := by
    by_contra hnot
    simp only [hnot, ↓reduceIte] at hspec
    rcases hspec with ⟨⟨hnone, _⟩, _, _⟩
    cases hnone
  have hspec' := hspec
  simp only [hstart, ↓reduceIte] at hspec'
  rcases hspec' with ⟨⟨hopt, _⟩, _, _⟩
  have hstartEq : start = iter.iter.start := by
    have h := Option.some.inj hopt
    exact h
  have hstart26 : start.val < 26 := by rw [hstartEq]; omega
  have hwidth := AspisR1FastDotsBatchRangeBound.width_le_four
    start batchEndArg rangeEnd hstart26 hadd hmin
  subst start
  exact ⟨rangeEnd, sums1, hwidth, hterms⟩

#print axioms body_success_term_range_width
end AspisR1FastDotsBatchActualRange
