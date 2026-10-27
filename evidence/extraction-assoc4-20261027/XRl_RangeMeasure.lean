import XRk_ABI
open Aeneas Aeneas.Std Result
namespace XRl_RangeMeasure
abbrev iterator := core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize
def remaining (s : core.ops.range.Range Usize) := s.end.val-s.start.val

theorem terminal (s next : core.ops.range.Range Usize)
    (run : iterator.next s=ok (none,next)) : remaining s=0 := by
  by_cases active : s.start.val < s.end.val
  · obtain ⟨⟨value,state⟩,step,hvalue,_,_⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_some_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x; rfl) (by intro x y; rfl)
        s active)
    have same := Result.ok.inj (step.symm.trans run)
    have bad := congrArg Prod.fst same
    rw [hvalue] at bad
    cases bad
  · unfold remaining
    omega

theorem advance (s next : core.ops.range.Range Usize) (value : Usize)
    (run : iterator.next s=ok (some value,next)) : remaining s=remaining next+1 := by
  by_cases active : s.start.val < s.end.val
  · obtain ⟨⟨v,state⟩,step,hv,hs,he⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_some_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x; rfl) (by intro x y; rfl)
        s active)
    have same := Result.ok.inj (step.symm.trans run)
    have stateeq := congrArg Prod.snd same
    change state=next at stateeq
    subst state
    unfold remaining
    rw [he]
    omega
  · obtain ⟨⟨v,state⟩,step,hv,_⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y; rfl)
        s (by omega))
    have same := Result.ok.inj (step.symm.trans run)
    have bad := congrArg Prod.fst same
    rw [hv] at bad
    cases bad
#print axioms terminal
#print axioms advance
end XRl_RangeMeasure
