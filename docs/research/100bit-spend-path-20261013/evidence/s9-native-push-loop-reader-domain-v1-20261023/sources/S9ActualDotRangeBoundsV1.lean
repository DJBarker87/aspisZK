import S9RangeNextProgressV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualDotRangeBoundsV1
abbrev Iter := core.ops.range.Range Usize
/-- Exact yielded index, in addition to the previously proved progress law. -/
theorem range_next_index_bounds (iter iterNext : Iter) (j : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j,iterNext)) :
    j = iter.start ∧ j.val < iter.end.val ∧
      iterNext.start.val = iter.start.val+1 ∧ iterNext.end = iter.end := by
  obtain ⟨hlt,hstart,hend⟩ :=
    AspisR1S9RangeNextProgressV2.range_next_some_progress iter iterNext j hnext
  obtain ⟨pair,hspec,hpost⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize)
      (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) iter hlt)
  have heq := Result.ok.inj (hspec.symm.trans hnext)
  have hitem : pair.1 = some j := congrArg Prod.fst heq
  have hj : j=iter.start := Option.some.inj (hitem.symm.trans hpost.1)
  exact ⟨hj,by simpa only [hj] using hlt,hstart,hend⟩
#print axioms range_next_index_bounds
end AspisR1S9ActualDotRangeBoundsV1
