import NDO_JHd_RequestValue
import NDO_JHd_RequestWindow
set_option autoImplicit false
namespace AspisR1.JHd_RequestBindings
open Aeneas Aeneas.Std Result JHd_RequestWindow

theorem profile : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    value {start:=8#usize,«end»:=40#usize}=ok (window 8 32 (by decide)) :=
  range 8#usize 40#usize (by decide) (by decide)
theorem release : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    value {start:=40#usize,«end»:=72#usize}=ok (window 40 32 (by decide)) :=
  range 40#usize 72#usize (by decide) (by decide)
theorem pool : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    value {start:=72#usize,«end»:=104#usize}=ok (window 72 32 (by decide)) :=
  range 72#usize 104#usize (by decide) (by decide)
#print axioms profile
#print axioms release
#print axioms pool

theorem profile_cast : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (window 8 32 (by decide))=ok (.Ok JHd_RequestValue.value.verifier_profile) := by
  apply JFt_ExactArray.cast
  exact JHb_RequestBindings.profile
#print axioms profile_cast

theorem release_cast : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (window 40 32 (by decide))=ok (.Ok JHd_RequestValue.value.verifier_release) := by
  apply JFt_ExactArray.cast
  exact JHb_RequestBindings.release
#print axioms release_cast

theorem pool_cast : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (window 72 32 (by decide))=ok (.Ok JHd_RequestValue.value.pool_program) := by
  apply JFt_ExactArray.cast
  exact JHb_RequestBindings.pool
#print axioms pool_cast
end AspisR1.JHd_RequestBindings
