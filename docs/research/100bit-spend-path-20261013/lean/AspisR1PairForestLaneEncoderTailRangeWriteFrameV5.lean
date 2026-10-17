import AspisR1PairForestLaneEncoderTailPrefixFrameV7
import Aeneas.Std

set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailRangeWriteFrame
open Aeneas Aeneas.Std

/-- Every successful array range-index/copy pair has the exact backing setSlice! effect. -/
theorem range_copy_back_exact
    {N M : Usize} (base : Array U8 N) (bytes : Array U8 M)
    (target copied : Slice U8) (back : Slice U8 → Array U8 N)
    (r : core.ops.range.Range Usize)
    (h0 : r.start ≤ r.end) (h1 : r.end ≤ N)
    (hlen : bytes.length = r.end.val - r.start.val)
    (hindex : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice U8)) base r = .ok (target, back))
    (hcopy : core.slice.Slice.copy_from_slice core.marker.CopyU8 target
      (Array.to_slice bytes) = .ok copied) :
    (back copied).val = base.val.setSlice! r.start.val bytes.val := by
  have hspec := Array.index_mut_SliceIndexRangeUsizeSlice.step base r h0 h1
  rw [hindex] at hspec
  simp only [WP.spec_ok] at hspec
  rcases hspec with ⟨hval, hlen', hback⟩
  have hsourceLen : (Array.to_slice bytes).length = r.end.val - r.start.val := by
    simpa [Array.to_slice, Slice.length] using hlen
  have hcopyLen : target.length = (Array.to_slice bytes).length := hlen'.trans hsourceLen.symm
  have hcopySpec := core.slice.Slice.copy_from_slice.step_spec
    core.marker.CopyU8 target (Array.to_slice bytes) hcopyLen
  rw [hcopy] at hcopySpec
  simp only [WP.spec_ok] at hcopySpec
  rw [hback, hcopySpec]
  simp [Array.to_slice]

/-- A range write beginning after a queried prefix leaves that prefix byte-for-byte intact. -/
theorem range_copy_preserves_prefix
    {N M : Usize} (base : Array U8 N) (bytes : Array U8 M)
    (target copied : Slice U8) (back : Slice U8 → Array U8 N)
    (r : core.ops.range.Range Usize)
    (h0 : r.start ≤ r.end) (h1 : r.end ≤ N)
    (hlen : bytes.length = r.end.val - r.start.val)
    (hindex : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice U8)) base r = .ok (target, back))
    (hcopy : core.slice.Slice.copy_from_slice core.marker.CopyU8 target
      (Array.to_slice bytes) = .ok copied)
    (j : Nat) (hj : j < r.start.val) :
    (back copied).val[j]? = base.val[j]? := by
  rw [range_copy_back_exact base bytes target copied back r h0 h1 hlen hindex hcopy]
  exact List.setSlice!_getElem?_prefix base.val bytes.val r.start.val j hj

#print axioms range_copy_back_exact
#print axioms range_copy_preserves_prefix

/-- Slice-valued variant for generated `lift (Array.to_slice bytes)` writes. -/
theorem range_copy_preserves_prefix_slice
    {N : Usize} (base : Array U8 N) (source target copied : Slice U8)
    (back : Slice U8 → Array U8 N) (r : core.ops.range.Range Usize)
    (h0 : r.start ≤ r.end) (h1 : r.end ≤ N)
    (hlen : source.length = r.end.val - r.start.val)
    (hindex : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeUsizeSlice U8)) base r = .ok (target, back))
    (hcopy : core.slice.Slice.copy_from_slice core.marker.CopyU8 target source = .ok copied)
    (j : Nat) (hj : j < r.start.val) :
    (back copied).val[j]? = base.val[j]? := by
  have hspec := Array.index_mut_SliceIndexRangeUsizeSlice.step base r h0 h1
  rw [hindex] at hspec
  simp only [WP.spec_ok] at hspec
  rcases hspec with ⟨hval, hlen', hback⟩
  have hcopyLen : target.length = source.length := by omega
  have hcopySpec := core.slice.Slice.copy_from_slice.step_spec
    core.marker.CopyU8 target source hcopyLen
  rw [hcopy] at hcopySpec
  simp only [WP.spec_ok] at hcopySpec
  rw [hback, hcopySpec]
  exact List.setSlice!_getElem?_prefix base.val source.val r.start.val j hj

#print axioms range_copy_preserves_prefix_slice
end AspisR1PairForestLaneEncoderTailRangeWriteFrame
