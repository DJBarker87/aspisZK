import Aeneas.Std
import RPv_Qm31PackBase4SliceFacts

/-! The exact length-four source-array boundary used by the generated packer.
These facts expose existing Aeneas step specifications and the resulting
backing-list update; no field arithmetic or caller-length fact is assumed. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskQmPackBase4Array

open Aeneas Aeneas.Std

theorem range_mut_back_source {α : Type} (base : Array α 4#usize)
    (source : Slice α) (back : Slice α → Array α 4#usize)
    (hsource : source.length = 4)
    (hback : ∀ s', (back s').val = base.val.setSlice! 0 s'.val) :
    (back source).val = source.val := by
  rw [hback source]
  exact AspisR1.Qm31PackBase4SliceFacts.setSlice_zero_eq_source
    base.val source.val (by simpa using base.property) hsource

theorem copy_from_slice_spec {α : Type} (copyInst : core.marker.Copy α)
    (front source : Slice α) (hlen : front.length = source.length) :
    core.slice.Slice.copy_from_slice copyInst front source
      ⦃ output => output = source ⦄ :=
  core.slice.Slice.copy_from_slice.step_spec copyInst front source hlen

theorem range_mut_four_step {α : Type} (base : Array α 4#usize)
    (r : core.ops.range.RangeTo Usize) (hr : r.end.val = 4) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice α)) base r
      ⦃ (s : Slice α) (back : Slice α → Array α 4#usize) =>
        s.val = base.val.slice 0 r.end ∧ s.length = 4 ∧
        ∀ s', (back s').val = base.val.setSlice! 0 s'.val ⦄ := by
  have hbound : r.end ≤ (4#usize : Usize) := by scalar_tac
  simpa [hr] using Array.index_mut_SliceIndexRangeToUsizeSlice base r hbound

#print axioms range_mut_back_source
#print axioms copy_from_slice_spec
#print axioms range_mut_four_step

end AspisR1.ExtractedMaskQmPackBase4Array
