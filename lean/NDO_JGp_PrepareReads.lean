import NDO_JGn_PrepareBuffer
import NDO_JFw_Range
set_option autoImplicit false
namespace AspisR1.JGp_PrepareReads
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes JFw_Frames.window

theorem semantic :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.proof {start:=16#usize,«end»:=7031#usize}=ok JFw_RealExpansion.stored := by
  have same : JFw_Frames.window 16 7015=JFw_RealExpansion.stored := by
    unfold JFw_Frames.window JFw_RealExpansion.stored
    rfl
  have h := JFw_Range.read 16#usize 7031#usize (by decide) (by decide)
  change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=16#usize,«end»:=7031#usize}=ok (JFw_Frames.window 16 7015) at h
  rw [same] at h
  exact h
#print axioms semantic

theorem y1 :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.proof {start:=7031#usize,«end»:=7495#usize}=ok JFw_Y1.stored := by
  have h := JFw_Range.read 7031#usize 7495#usize (by decide) (by decide)
  change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=7031#usize,«end»:=7495#usize}=ok (JFw_Frames.window 7031 464) at h
  exact h
#print axioms y1

end AspisR1.JGp_PrepareReads
