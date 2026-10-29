import Aeneas.Std.RangeIter
set_option autoImplicit false
namespace NCJ_ForwardRange
open Aeneas Aeneas.Std Result
abbrev Range := core.ops.range.Range Usize
abbrev next := core.iter.range.IteratorRange.next core.iter.range.StepUsize

theorem done (iter : Range) (stop : iter.end.val≤ iter.start.val) : next iter=ok (none,iter) := by
  obtain ⟨out,run,hspec⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intros;rfl) iter stop)
  rcases out with ⟨opt,rest⟩
  rcases hspec with ⟨ho,hr⟩
  cases ho
  cases hr
  exact run

theorem active (iter : Range) (h : iter.start.val< iter.end.val) :
    ∃ rest,next iter=ok (some iter.start,rest) ∧
      rest.start.val=iter.start.val+1 ∧ rest.end=iter.end := by
  obtain ⟨out,run,hspec⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
      (by intros;rfl) (by intros;rfl) iter h)
  rcases out with ⟨opt,rest⟩
  rcases hspec with ⟨ho,hs,he⟩
  cases ho
  exact ⟨rest,run,hs,he⟩

theorem exact_step (iter : Range) (nextStart : Usize)
    (active : iter.start.val< iter.end.val) (value : nextStart.val=iter.start.val+1) :
    next iter=ok (some iter.start,{start:=nextStart,«end»:=iter.end}) := by
  obtain ⟨rest,run,start,finish⟩ := NCJ_ForwardRange.active iter active
  have hs : rest.start=nextStart := UScalar.eq_of_val_eq (start.trans value.symm)
  have same : rest={start:=nextStart,«end»:=iter.end} := by
    cases rest
    simp_all
  simpa only [same] using run

#print axioms done
#print axioms active
#print axioms exact_step
end NCJ_ForwardRange
