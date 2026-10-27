import FIo_LoopInvariant
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_RangeNext
open Aeneas Aeneas.Std Result
abbrev Range := core.ops.range.Range Usize

theorem some_next (r r' : Range) (i : Usize)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize r=ok (some i,r')) :
    i=r.start ∧ r'.end=r.end ∧ r'.start.val=r.start.val+1 ∧ r.start.val<r.end.val := by
  simp only [core.iter.range.IteratorRange.next,core.iter.range.StepUsize,
    core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,core.cmp.impls.PartialOrdUsize.lt,
    core.clone.CloneUsize,liftFun2,lift,bind_tc_ok] at run
  split at run
  · rename_i more
    simp only [core.clone.impls.CloneUsize.clone,bind_tc_ok,
      core.iter.range.UScalarStep.forward_checked] at run
    split at run
    · have same := Result.ok.inj run
      cases same
      exact ⟨rfl,rfl,by simp,by simpa using more⟩
    · cases run
  · cases run

#print axioms some_next
end AspisR1.FIo_RangeNext
end
