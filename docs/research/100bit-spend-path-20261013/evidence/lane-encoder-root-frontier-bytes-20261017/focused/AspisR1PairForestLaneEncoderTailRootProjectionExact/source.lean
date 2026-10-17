import AspisR1PairForestLaneEncoderTailSourceCut.Funs
import Aeneas.Std

set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailRootProjection
open Aeneas Aeneas.Std

/-- The root writer's exact range-copy contract, isolated from the later frontier writes. -/
theorem root_range_copy_back_exact
    (base : Array U8 768#usize) (target copied : Slice U8)
    (back : Slice U8 → Array U8 768#usize)
    (bytes : Array U8 32#usize)
    (hindex : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice U8)) base
      { start := 96#usize, «end» := 128#usize } = .ok (target, back))
    (hcopy : core.slice.Slice.copy_from_slice core.marker.CopyU8 target
      (Array.to_slice bytes) = .ok copied) :
    (back copied).val = base.val.setSlice! 96 bytes.val := by
  have hspec := Array.index_mut_SliceIndexRangeUsizeSlice.step base
    { start := 96#usize, «end» := 128#usize } (by scalar_tac) (by scalar_tac)
  rw [hindex] at hspec
  simp only [WP.spec_ok] at hspec
  rcases hspec with ⟨hval, hlen, hback⟩
  have hcopySpec := core.slice.Slice.copy_from_slice.step_spec
    core.marker.CopyU8 target (Array.to_slice bytes) (by
      simp [Array.to_slice, Slice.length, hlen])
  rw [hcopy] at hcopySpec
  simp only [WP.spec_ok] at hcopySpec
  have hdata : (back copied).val = base.val.setSlice! 96 bytes.val := by
    rw [hback, hcopySpec]
    simp [Array.to_slice]
  exact hdata

#print axioms root_range_copy_back_exact
end AspisR1PairForestLaneEncoderTailRootProjection
