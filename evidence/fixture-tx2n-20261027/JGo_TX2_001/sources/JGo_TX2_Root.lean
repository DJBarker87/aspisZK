import JGm_TX2_Batch
import JGe_View
import JFw_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Root
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes

theorem selected : JGe_View.folded=JGc_TX2_Obstruction70.folded := by
  apply Subtype.ext
  exact JGc_TX2_M2Root.selected_root
#print axioms selected

theorem read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7751#usize,«end»:=7783#usize}=
      ok (JFw_Frames.window 7751 32) :=
  JFw_Range.read 7751#usize 7783#usize (by decide) (by decide)
#print axioms read

theorem array : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (JFw_Frames.window 7751 32)=ok (.Ok JGc_TX2_Obstruction70.folded) := by
  have size : Slice.len (JFw_Frames.window 7751 32)=32#usize := by
    apply UScalar.eq_of_val_eq
    exact JFw_Frames.window_length 7751 32 (by decide)
  unfold core.array.TryFromArrayCopySlice.try_from
  rw [dif_pos size]
  exact congrArg (fun r => ok (.Ok r)) selected
#print axioms array
end AspisR1.JGo_TX2_Root
end
