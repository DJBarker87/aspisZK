import NDO_JGp_PrepareReads
import NDO_JGe_View
set_option autoImplicit false
namespace AspisR1.JGp_FoldedRead
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes JFw_Frames.window

theorem range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7751#usize,«end»:=7783#usize}=ok (JFw_Frames.window 7751 32) := by
  have read := JFw_Range.read 7751#usize 7783#usize (by decide) (by decide)
  change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7751#usize,«end»:=7783#usize}=ok (JFw_Frames.window 7751 32) at read
  exact read
#print axioms range

theorem copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (JFw_Frames.window 7751 32)=ok (.Ok JGe_View.folded) := by
  obtain ⟨r,call,fields⟩ := WP.spec_imp_exists (core.array.TryFromArrayCopySlice.try_from.step
    32#usize core.marker.CopyU8 (JFw_Frames.window 7751 32))
  have size : (JFw_Frames.window 7751 32).length=32 := JFw_Frames.window_length 7751 32 (by decide)
  cases r with
  | Err e =>
    simp only [size] at fields
    exact False.elim (fields rfl)
  | Ok root =>
    have same : root=JGe_View.folded := Subtype.ext fields.1
    exact same ▸ call
#print axioms copy
end AspisR1.JGp_FoldedRead
