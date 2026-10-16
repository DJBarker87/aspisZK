import SumHighInnerLoop
import ExtractedMaskConstants

/-! Actual shared source sum_high wrapper for one bounded contiguous range.
This is the range shape used by the path selector prefix. -/
set_option autoImplicit false
namespace AspisR1.SumHighSingleRange
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SumHighInnerLoop
open AspisR1.ExtractedMaskConstants

abbrev SliceIter := core.slice.iter.Iter Range
abbrev Outer := AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0

def singleton (r : Range) : Slice Range := Array.to_slice (Array.make 1#usize [r])

def iterAt (r : Range) (i : Nat) : SliceIter := { slice := singleton r, i := i }

private theorem next_first (r : Range) :
    core.slice.iter.IteratorSliceIter.next (iterAt r 0) = .ok (some r, iterAt r 1) := by
  simp [iterAt, singleton, core.slice.iter.IteratorSliceIter.next,
    Slice.len, Slice.length, Array.to_slice, Array.make]

private theorem next_last (r : Range) :
    core.slice.iter.IteratorSliceIter.next (iterAt r 1) = .ok (none, iterAt r 1) := by
  simp [iterAt, singleton, core.slice.iter.IteratorSliceIter.next,
    Slice.len, Slice.length, Array.to_slice, Array.make]

private theorem outer_done (r : Range) (selectors : Selectors) (acc : QM) :
    Outer (iterAt r 1) selectors acc = .ok acc := by
  change AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0
    (iterAt r 1) selectors acc = .ok acc
  rw [AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0.eq_def]
  simp only [next_last, bind_tc_ok]

theorem singleton_success (r : Range) (selectors : Selectors)
    (hstart : r.start.val ≤ r.end.val) (hend : r.end.val ≤ 64)
    (hhigh : CanonicalArray selectors.high) :
    ∃ out,
      AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high
        selectors (singleton r) = .ok out ∧ Canonical out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        sumModel selectors (r.end.val - r.start.val) r.start.val 0 := by
  obtain ⟨out, hinner, hcanonical, hmodel⟩ :=
    loop_model (r.end.val - r.start.val) r selectors field.QM31.ZERO hend
      (by omega) hhigh zero_canonical
  refine ⟨out, ?_, hcanonical, ?_⟩
  · unfold AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high
    simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
      bind_tc_ok]
    change Outer (iterAt r 0) selectors field.QM31.ZERO = .ok out
    change AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0
      (iterAt r 0) selectors field.QM31.ZERO = .ok out
    rw [AspisR1SumHighCandidate.pool_v1.pair_forest_semantic_terminal.sum_high_loop0.eq_def]
    simp only [next_first, bind_tc_ok, AspisR1SumHighCandidate.clone_usize, hinner,
      outer_done]
  · simpa only [zero_decode] using hmodel

#print axioms singleton_success
end
end AspisR1.SumHighSingleRange
