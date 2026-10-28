import NDO_JFs_RangeFrom
import NDO_JFt_ExactArray
set_option autoImplicit false
namespace AspisR1.JFs_ArrayWindow
open Aeneas Aeneas.Std Result

def array (off : Nat) (n : Usize) (bound : off+n.val≤1880) : Array U8 n :=
  ⟨(JFu_PublicRange.segment off n.val bound).val,JFu_PublicRange.length off n.val bound⟩

theorem range (off : Nat) (n : Usize) (bound : off+n.val≤1880) (start stop : Usize)
    (order : start.val≤stop.val) (inside : stop.val≤n.val) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      (array off n bound) {start:=start,«end»:=stop}=
      ok (JFu_PublicRange.segment (off+start.val) (stop.val-start.val) (by omega)) := by
  unfold core.array.Array.index core.ops.index.IndexSlice array
  exact JFt_Range.read off n.val bound start stop order inside

theorem suffix (off : Nat) (n : Usize) (bound : off+n.val≤1880) (start : Usize)
    (inside : start.val≤n.val) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
      (array off n bound) {start:=start}=
      ok (JFu_PublicRange.segment (off+start.val) (n.val-start.val) (by omega)) := by
  unfold core.array.Array.index core.ops.index.IndexSlice array
  exact JFs_RangeFrom.read off n.val bound start inside

theorem shared (N : Usize) (bytes : Slice U8) (arr : Array U8 N) (same : bytes.val=arr.val) :
    core.array.TryFromSharedArraySlice.try_from N bytes=ok (.Ok arr) := by
  have size : Slice.len bytes=N := by
    have h : bytes.length=N.val := by change bytes.val.length=N.val;rw [same,arr.property]
    scalar_tac
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dif_pos size]
  apply congrArg ok
  apply congrArg core.result.Result.Ok
  exact Subtype.ext same

#print axioms range
#print axioms suffix
#print axioms shared
end AspisR1.JFs_ArrayWindow
