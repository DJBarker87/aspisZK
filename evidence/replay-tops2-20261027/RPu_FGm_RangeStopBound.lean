import RPu_FGm_RangeDone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_RangeStopBound
open Aeneas Aeneas.Std Result

theorem eq (r r' : FIo_RangeNext.Range) (n : Usize)
    (hend : r.end=n) (bound : r.start.val≤n.val)
    (run : core.iter.range.IteratorRange.next core.iter.range.StepUsize r=ok (none,r')) :
    r.start.val=n.val := by
  have stop := FGm_RangeDone.done_next r r' run
  rw [hend] at stop
  exact Nat.le_antisymm bound stop

#print axioms eq
end AspisR1.FGm_RangeStopBound
end
