import PV_EVH_NativeEntropyBorrow
set_option autoImplicit false
namespace PV_EVH_EntropyHalves
open Aeneas Aeneas.Std ProverRwFull

/-- Symbolic halves of the original delivered array, with no concrete entropy
reduction and no choice of a different backing allocation. -/
def field (a : Array U8 64#usize) : Array U8 32#usize :=
  ⟨a.val.take 32, by simpa [a.property] using List.length_take 32 a.val⟩

def seed (a : Array U8 64#usize) : Array U8 32#usize :=
  ⟨a.val.drop 32, by simp [a.property]⟩

theorem first_index (a : Array U8 64#usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice U8)) a { «end» := 32#usize } =
      .ok (Array.to_slice (field a)) := by
  simp [core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    Array.to_slice,Slice.length,field,List.slice,a.property]

theorem second_index (a : Array U8 64#usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice U8)) a { start := 32#usize } =
      .ok (Array.to_slice (seed a)) := by
  simp [core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.Slice.index,core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    Array.to_slice,Slice.length,Slice.drop,seed,a.property]

theorem copy32 (before after : Array U8 32#usize) :
    core.slice.Slice.copy_from_slice core.marker.CopyU8
      (Array.to_slice_mut before).1 (Array.to_slice after) =
      .ok (Array.to_slice after) := by
  simp [core.slice.Slice.copy_from_slice,Array.to_slice_mut,Array.to_slice,
    Slice.len,before.property,after.property]

/-- Both mutable restoration continuations retain the copied bytes. This is
an extensional source law; machine frame/alias and copy-residue laws stay P. -/
theorem restored (before after : Array U8 32#usize) :
    (Array.to_slice_mut before).2 (Array.to_slice after) = after :=
  PV_EVH_NativeEntropyBorrow.restore_array _ before after

theorem halves_reconstruct (a : Array U8 64#usize) :
    (field a).val ++ (seed a).val = a.val := List.take_append_drop 32 a.val

#print axioms first_index
#print axioms second_index
#print axioms copy32
#print axioms restored
#print axioms halves_reconstruct
end PV_EVH_EntropyHalves
