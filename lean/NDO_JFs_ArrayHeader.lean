import NDO_JFs_ArrayWindow
import NDO_JFt_LocalWindow
set_option autoImplicit false
namespace AspisR1.JFs_ArrayHeader
open Aeneas Aeneas.Std Result

theorem firstn (off : Nat) (n : Usize) (bound : off+n.val≤1880) (count : Usize)
    (inside : count.val≤n.val) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
      (JFs_ArrayWindow.array off n bound) {«end»:=count}=
      ok (JFu_PublicRange.segment off count.val (by omega)) := by
  unfold core.array.Array.index core.ops.index.IndexSlice JFs_ArrayWindow.array
  exact JFt_LocalWindow.firstn off n.val count bound inside

theorem index (off : Nat) (n : Usize) (bound : off+n.val≤1880) (i : Usize) :
    Array.index_usize (JFs_ArrayWindow.array off n bound) i=
    Slice.index_usize (JFu_PublicRange.segment off n.val bound) i := by rfl

#print axioms firstn
#print axioms index
end AspisR1.JFs_ArrayHeader
