import NDO_JFs_ArrayWindow
import NDO_JFs_IndexWindow
import NDO_JFu_PublicMeta07
set_option autoImplicit false
namespace AspisR1.JFs_PaymentArray
open Aeneas Aeneas.Std Result

def value : Array U8 216#usize := JFs_ArrayWindow.array 1664 216#usize (by decide)

theorem shared : core.array.TryFromSharedArraySlice.try_from 216#usize JFu_PublicRange.payment=
    ok (.Ok value) := by
  apply JFs_ArrayWindow.shared
  simp only [value,JFs_ArrayWindow.array,JFu_PublicRange.payment,show (216#usize).val=216 from rfl]

theorem range (start stop : Usize) (order : start.val≤stop.val) (inside : stop.val≤216) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      value {start:=start,«end»:=stop}=
      ok (JFu_PublicRange.segment (1664+start.val) (stop.val-start.val) (by omega)) :=
  JFs_ArrayWindow.range 1664 216#usize (by decide) start stop order inside

theorem suffix (start : Usize) (inside : start.val≤216) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
      value {start:=start}=
      ok (JFu_PublicRange.segment (1664+start.val) (216-start.val) (by omega)) :=
  JFs_ArrayWindow.suffix 1664 216#usize (by decide) start inside

#print axioms shared
#print axioms range
#print axioms suffix
end AspisR1.JFs_PaymentArray
