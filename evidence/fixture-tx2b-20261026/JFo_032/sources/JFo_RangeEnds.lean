import JFo_PrefixRead
import JFo_SuffixRead
set_option autoImplicit false
namespace AspisR1.JFo_RangeEnds
open Aeneas Aeneas.Std Result

theorem drop_take {A : Type} (xs : List A) (start n : Nat) (size : xs.length=start+n) :
    xs.drop start = (xs.drop start).take n := by
  rw [List.take_of_length_le]
  simp only [List.length_drop,size]
  omega

theorem suffix : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
    JFx_NativeBytes.checkpoint {start:=1736#usize}=ok (JFq_Range.segment 1736 32 (by decide)) := by
  apply JFo_SuffixRead.source
  · change 1736≤JFx_NativeBytes.checkpoint.val.length
    have size : JFx_NativeBytes.checkpoint.val.length=1768 := JFx_NativeBytes.checkpointBytes_length
    omega
  · exact drop_take JFx_NativeBytes.checkpoint.val 1736 32 JFx_NativeBytes.checkpointBytes_length

theorem leading : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    JFx_NativeBytes.checkpoint {«end»:=1736#usize}=ok (JFq_Range.segment 0 1736 (by decide)) := by
  apply JFo_PrefixRead.source
  · change 1736≤JFx_NativeBytes.checkpoint.val.length
    have size : JFx_NativeBytes.checkpoint.val.length=1768 := JFx_NativeBytes.checkpointBytes_length
    omega
  · exact (congrArg (fun xs : List U8 => xs.take 1736) (List.drop_zero JFx_NativeBytes.checkpoint.val)).symm

#print axioms drop_take
#print axioms suffix
#print axioms leading
end AspisR1.JFo_RangeEnds
