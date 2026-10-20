import Aeneas.Std.RangeIter

/-! Focused reuse of the already-checked Aeneas forward-range WP proofs from
`ExtractedMaskForwardRange`: the occupancy literal loop consumes precisely
these `Range Usize` step/termination facts. -/
set_option autoImplicit false
namespace AspisR1.OccupancyRangeTraversal
open Aeneas Aeneas.Std Result ControlFlow
abbrev Range := core.ops.range.Range Usize

/-- At or beyond the end, the actual forward iterator returns `none` and the
unchanged range. Reused verbatim from ExtractedMaskForwardRange.next_done. -/
theorem next_done (iter : Range) (hge : iter.start.val ≥ iter.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none, iter) := by
  obtain ⟨out, hrun, hspec⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_none_spec
      (partialOrdInst := core.cmp.PartialOrdUsize) (by intros; rfl) iter hge)
  rcases out with ⟨opt, iter1⟩
  rcases hspec with ⟨hopt, hiter⟩
  cases hopt
  cases hiter
  exact hrun

/-- Below the end, the iterator yields its old start and an incremented range.
Reused verbatim from ExtractedMaskForwardRange.next_step. -/
theorem next_step (iter : Range) (hlt : iter.start.val < iter.end.val) :
    ∃ iter1 : Range,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some iter.start, iter1) ∧
      iter1.start.val = iter.start.val + 1 ∧
      iter1.end = iter.end ∧
      iter.start.val + 1 ≤ Usize.max := by
  obtain ⟨out, hrun, hspec⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize)
      (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) iter hlt)
  rcases out with ⟨opt, iter1⟩
  rcases hspec with ⟨hopt, hstart, hend⟩
  cases hopt
  have hbound : iter.start.val + 1 ≤ Usize.max := by
    have hb : iter.start.val + 1 < 2 ^ System.Platform.numBits := by
      simpa [Usize.numBits, UScalarTy.numBits, hstart] using iter1.start.hBounds
    have hb' : iter.start.val + 1 ≤ 2 ^ System.Platform.numBits - 1 := by omega
    simpa [Usize.max, Usize.numBits, UScalarTy.numBits] using hb'
  exact ⟨iter1, hrun, hstart, hend, hbound⟩

#print axioms next_done
#print axioms next_step
end AspisR1.OccupancyRangeTraversal
