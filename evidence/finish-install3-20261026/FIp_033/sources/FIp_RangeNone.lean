import FIo_RangeNext
set_option autoImplicit false
namespace AspisR1.FIp_RangeNone
open Aeneas Aeneas.Std Result

theorem none_next (r r' : FIo_RangeNext.Range)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize r=ok (none,r')) :
    r.end.val≤r.start.val := by
  simp only [core.iter.range.IteratorRange.next,core.iter.range.StepUsize,
    core.iter.range.UScalarStep,core.cmp.PartialOrdUsize,core.cmp.impls.PartialOrdUsize.lt,
    core.clone.CloneUsize,liftFun2,lift,bind_tc_ok] at run
  split at run
  · simp only [core.clone.impls.CloneUsize.clone,bind_tc_ok,
      core.iter.range.UScalarStep.forward_checked] at run
    split at run <;> cases run
  · rename_i noMore
    have h : ¬r.start.val<r.end.val := by simpa only [UScalar.lt_equiv] using noMore
    omega

#print axioms none_next
end AspisR1.FIp_RangeNone
