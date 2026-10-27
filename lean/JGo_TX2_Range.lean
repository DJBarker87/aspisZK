import OccupancyRangeTraversal
import Port3_Wrapping
set_option autoImplicit false
namespace AspisR1.JGo_TX2_Range
open Aeneas Aeneas.Std Result

theorem next (i stop j : Usize) (more : i.val<stop.val) (inc : i.val+1=j.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize
      ({start:=i,«end»:=stop} : core.ops.range.Range Usize)=
        ok (some i,{start:=j,«end»:=stop}) := by
  obtain ⟨r,call,start,finish,_⟩ := OccupancyRangeTraversal.next_step
    ({start:=i,«end»:=stop} : core.ops.range.Range Usize) more
  have hs : r.start=j := UScalar.eq_of_val_eq (start.trans inc)
  have same : r=({start:=j,«end»:=stop} : core.ops.range.Range Usize) := by
    cases r
    simp_all only [core.ops.range.Range.mk.injEq]
  exact same ▸ call
#print axioms next
end AspisR1.JGo_TX2_Range
