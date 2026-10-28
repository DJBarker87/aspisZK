import NBP_Store
set_option autoImplicit false
noncomputable section
namespace NBP_PrefixStore
open Aeneas Aeneas.Std Result

theorem store_then {N W : Usize} {T : Type} (output : Array U8 N)
    (bytes : Array U8 W) (k : Array U8 N → Result T) (bound : W.val ≤ N.val) :
    (do
      let (s,back) ← core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
        output {«end»:=W}
      let src ← lift (Array.to_slice bytes)
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
      k (back copied)) = k (output.setSlice! 0 bytes.val) := by
  simp only [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,Array.to_slice]
  simp [Slice.length,Slice.len,bound,output.property,bytes.property,
    core.slice.Slice.copy_from_slice,List.slice,Nat.min_eq_left bound,
    Array.from_slice,lift]
#print axioms store_then
end NBP_PrefixStore
