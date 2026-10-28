import NDO_JGo_TX2_FieldRead
import Port3_Wrapping
import RPz7_FIo_Install
import NDO_JGe_Payload31
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_MessageRead
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof

theorem cell (i : Nat) (hi : i<64) :
    ((JFw_Frames.window 8007 2048).val.drop (32*i)).take 32=
      (JFw_Frames.window (8007+32*i) 32).val := by
  simp only [JFw_Frames.window,List.drop_take,List.drop_drop,List.take_take]
  rw [Nat.min_eq_left (by omega : 32≤2048-32*i)]
#print axioms cell

theorem range (bytes : Slice U8) (start stop : Usize) (arr : Array U8 32#usize)
    (order : start≤stop) (bound : stop.val≤bytes.length) (width : stop.val-start.val=32)
    (selected : (bytes.val.drop start.val).take 32=arr.val) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      {start:=start,«end»:=stop}=ok (Array.to_slice arr) := by
  obtain ⟨out,call,contents,size⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      (⟨start,stop⟩ : core.ops.range.Range Usize) bytes order bound)
  have same : out=Array.to_slice arr := by
    apply Subtype.ext
    rw [contents]
    change (bytes.val.drop start.val).take (stop.val-start.val)=arr.val
    rw [width,selected]
  exact same ▸ call
#print axioms range

theorem native (bytes : Slice U8) (i start next stop : Usize) (arr : Array U8 32#usize)
    (w : FIo_Install.NE)
    (mul : Usize.wrapping_mul i 32#usize=start)
    (add : Usize.wrapping_add i 1#usize=next)
    (mulStop : Usize.wrapping_mul next 32#usize=stop)
    (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=start,«end»:=stop}=ok (Array.to_slice arr))
    (parser : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes (Array.to_slice arr)=ok (some w)) :
    FIo_Native.weights.field bytes i=ok w := by
  simp only [FIo_Native.weights.field,mul,add,mulStop,lift,bind_tc_ok,read,parser]
  rfl
#print axioms native
end AspisR1.JGo_TX2_MessageRead
end
