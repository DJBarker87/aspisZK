import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ArrayTwoPrefixSourceV1

/-- The exact emitted Array::index(RangeTo{end=2}) operation used by the
S2 finish_relation call returns the whole two-element alpha array as a slice.
The source operation and range witness are retained, not replaced by an
assumed array/slice relation. -/
theorem array_two_prefix_exact {A : Type} (a : Array A 2#usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice A))
      a { «end» := 2#usize } = .ok (Array.to_slice a) := by
  change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice A)
    (Array.to_slice a) { «end» := 2#usize } = _
  have hn : a.val.length = 2 := a.property
  simp [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,Slice.length,List.slice,
    UScalar.le_equiv,Array.to_slice,hn]
  apply Subtype.ext
  change List.take 2 a.val = a.val
  simpa only [hn] using (show a.val.take a.val.length = a.val from List.take_length)

theorem successful_array_two_prefix_eq {A : Type}
    (a : Array A 2#usize) (selected : Slice A)
    (h : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice A))
      a { «end» := 2#usize } = .ok selected) : selected = Array.to_slice a := by
  exact (Result.ok.inj ((array_two_prefix_exact a).symm.trans h)).symm

/-- Full-prefix slicing preserves the exact successful read, including its
index and returned value. No independent readback/canonicality premise. -/
theorem successful_array_two_prefix_read {A : Type}
    (a : Array A 2#usize) (selected : Slice A)
    (h : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice A))
      a { «end» := 2#usize } = .ok selected) (i : Usize) :
    Slice.index_usize selected i = Array.index_usize a i := by
  rw [successful_array_two_prefix_eq a selected h]
  rfl

#print axioms array_two_prefix_exact
#print axioms successful_array_two_prefix_eq
#print axioms successful_array_two_prefix_read
end AspisR1S9ArrayTwoPrefixSourceV1
