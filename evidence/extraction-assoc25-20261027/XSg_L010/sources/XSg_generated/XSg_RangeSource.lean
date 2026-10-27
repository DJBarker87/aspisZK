import XSc_RangeMeasure
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSg_RangeSource
/-- Recover the actual cursor and next range from a reached source iteration. -/
theorem some (s next : core.ops.range.Range Usize) (j : Usize)
 (run : XSc_RangeMeasure.iterator.next s=ok (some j,next)) :
 j=s.start ∧ next.start.val=j.val+1 ∧ next.end=s.end ∧ j.val<s.end.val := by
 by_cases active : s.start.val<s.end.val
 · obtain ⟨⟨v,state⟩,step,hv,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl) s active)
   have same := Result.ok.inj (step.symm.trans run)
   have pair := Prod.mk.inj same
   have je : j=s.start := (Option.some.inj (hv.symm.trans pair.1)).symm
   have ne : state=next := pair.2
   subst state
   exact ⟨je,by simpa only [je] using hs,he,by simpa only [je] using active⟩
 · obtain ⟨⟨v,state⟩,step,hv,_⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) s (by omega))
   have same := congrArg Prod.fst (Result.ok.inj (step.symm.trans run))
   rw [hv] at same
   cases same
#print axioms some
end XSg_RangeSource
