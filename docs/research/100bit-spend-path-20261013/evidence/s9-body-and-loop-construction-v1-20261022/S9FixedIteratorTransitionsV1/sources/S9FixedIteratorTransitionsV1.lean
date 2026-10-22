import S9FactoredLoopTwoStepV4

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9FixedIteratorTransitionsV1
open AspisR1S9HelperP6
open AspisR1S9FactoredLoopTwoStepV4
abbrev U := Std.Usize
abbrev R := core.ops.range.Range U

private theorem range_eq (r s : R)
    (hs : r.start = s.start) (he : r.end = s.end) : r = s := by
  cases r
  cases s
  cases hs
  cases he
  rfl

theorem next_start0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize start0 =
      .ok (some 0#usize,start1) := by
  obtain ⟨pair, hn, hp⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) start0 (by decide))
  rcases pair with ⟨opt, iter⟩
  rcases hp with ⟨hopt, hs, he⟩
  subst opt
  have hs' : iter.start = start1.start := by
    apply UScalar.eq_of_val_eq
    simpa [start0,start1] using hs
  have he' : iter.end = start1.end := by simpa [start0,start1] using he
  have hi : iter = start1 := range_eq iter start1 hs' he'
  subst iter
  simpa only [start0] using hn

theorem next_start1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize start1 =
      .ok (some 1#usize,start2) := by
  obtain ⟨pair, hn, hp⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) start1 (by decide))
  rcases pair with ⟨opt, iter⟩
  rcases hp with ⟨hopt, hs, he⟩
  subst opt
  have hs' : iter.start = start2.start := by
    apply UScalar.eq_of_val_eq
    simpa [start1,start2] using hs
  have he' : iter.end = start2.end := by simpa [start1,start2] using he
  have hi : iter = start2 := range_eq iter start2 hs' he'
  subst iter
  simpa only [start1] using hn

theorem next_start2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize start2 =
      .ok (none,start2) := by
  obtain ⟨pair, hn, hp⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) start2 (by decide))
  rcases pair with ⟨opt, iter⟩
  rcases hp with ⟨hopt, hi⟩
  subst opt
  subst iter
  exact hn

#print axioms next_start0
#print axioms next_start1
#print axioms next_start2
end AspisR1S9FixedIteratorTransitionsV1
