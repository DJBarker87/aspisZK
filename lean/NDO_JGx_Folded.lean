import NDO_JGe_View
import NDO_JFw_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Folded
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes JFw_Frames.window

theorem read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7751#usize,«end»:=7783#usize}=
      ok (JFw_Frames.window 7751 32) :=
  by
    have h := JFw_Range.read 7751#usize 7783#usize (by decide) (by decide)
    simpa only [show (7751#usize).val=7751 from rfl,show (7783#usize).val=7783 from rfl,Nat.reduceSub] using h
#print axioms read

theorem array : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (JFw_Frames.window 7751 32)=ok (.Ok JGe_View.folded) := by
  have size : (JFw_Frames.window 7751 32).length=(32#usize).val :=
    JFw_Frames.window_length 7751 32 (by decide)
  unfold core.array.TryFromArrayCopySlice.try_from
  rw [dif_pos size]
  apply congrArg Result.ok
  apply congrArg core.result.Result.Ok
  apply Subtype.ext
  rfl
#print axioms array
end AspisR1.JGx_Folded
end
