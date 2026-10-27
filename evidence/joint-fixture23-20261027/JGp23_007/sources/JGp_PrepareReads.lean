import JGn_PrepareBuffer
import JFw_Range
set_option autoImplicit false
namespace AspisR1.JGp_PrepareReads
open Aeneas Aeneas.Std Result

theorem semantic :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.proof {start:=16#usize,«end»:=7031#usize}=ok JFw_RealExpansion.stored := by
  exact JFw_Range.read 16#usize 7031#usize (by scalar_tac) (by decide)
#print axioms semantic

theorem y1 :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.proof {start:=7031#usize,«end»:=7495#usize}=ok JFw_Y1.stored := by
  exact JFw_Range.read 7031#usize 7495#usize (by scalar_tac) (by decide)
#print axioms y1

#print alloc.vec.Vec.index
#print core.slice.index.SliceIndexRangeToUsizeSlice.index
#print core.slice.index.SliceIndexRangeFromUsizeSlice.index
#check AspisS1NativeCompactLengths.semantic_length
#check AspisR1CurrentCaller.InstalledPreparation.sourceView_semantic
end AspisR1.JGp_PrepareReads
