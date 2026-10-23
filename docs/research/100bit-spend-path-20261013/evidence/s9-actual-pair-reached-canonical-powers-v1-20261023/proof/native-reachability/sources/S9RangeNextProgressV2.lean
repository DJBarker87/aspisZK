import Aeneas
import Aeneas.Std.RangeIter
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9RangeNextProgressV2
abbrev Iter := core.ops.range.Range Std.Usize
theorem range_next_some_progress (iter iterNext : Iter) (j : Std.Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j, iterNext)) :
    iter.start.val < iter.end.val ∧
      iterNext.start.val = iter.start.val + 1 ∧
      iterNext.end = iter.end := by
  obtain ⟨pair, hspec, hpost⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_spec
      (cloneInst := core.clone.CloneUsize)
      (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) iter)
  rcases pair with ⟨opt, iter'⟩
  have hpair : (opt, iter') = (some j, iterNext) :=
    Result.ok.inj (hspec.symm.trans hnext)
  have hend := hpost.2
  by_cases hlt : iter.start.val < iter.end.val
  · have hbranches := hpost.1
    simp only [hlt, ↓reduceIte] at hbranches
    rcases hbranches with ⟨hopt, hstart⟩
    have hi : iter' = iterNext := by
      injection hpair with hopt' hiter
    have hstart' : iterNext.start.val = iter.start.val + 1 := by
      rw [← hi]
      exact hstart
    have hend' : iterNext.end = iter.end := by
      rw [← hi]
      exact hend
    exact ⟨hlt, hstart', hend'⟩
  · have hbranches := hpost.1
    simp only [hlt, ↓reduceIte] at hbranches
    rcases hbranches with ⟨hopt, _⟩
    injection hpair with hopt' _
    cases hopt'.symm.trans hopt


#print axioms range_next_some_progress
end AspisR1S9RangeNextProgressV2
