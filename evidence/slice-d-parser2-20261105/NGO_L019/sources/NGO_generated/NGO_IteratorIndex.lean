import NGO_IteratorStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_IteratorIndex
open NGO_IteratorStep
/-- Exact index, start and end facts from the original emitted next call. -/
theorem from_some (iter nextIter : Index) (index : Usize)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (some index,nextIter)) :
    index=iter.start ∧ nextIter.start.val=iter.start.val+1 ∧
      nextIter.end=iter.end ∧ iter.start.val<iter.end.val := by
  by_cases live : iter.start.val<iter.end.val
  · obtain ⟨⟨o,it⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_some_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
        iter live)
    rw [next] at run
    obtain ⟨same,eq⟩ := Prod.mk.inj (Result.ok.inj run)
    subst it
    exact ⟨Option.some.inj (same.trans ho),hs,he,live⟩
  · obtain ⟨⟨o,it⟩,run,ho,hi⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl)
        iter (by omega))
    rw [next] at run
    have same := congrArg Prod.fst (Result.ok.inj run)
    simp_all
#print axioms from_some
end NGO_IteratorIndex
