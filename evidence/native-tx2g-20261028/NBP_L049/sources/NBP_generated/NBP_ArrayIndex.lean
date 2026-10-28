import Aeneas
set_option autoImplicit false
namespace NBP_ArrayIndex
open Aeneas Aeneas.Std Result

def slice {N : Usize} (output : Array U8 N) (start stop : Usize) : Slice U8 :=
  ⟨output.val.slice start.val stop.val, by scalar_tac⟩

theorem index_mut {N : Usize} (output : Array U8 N) (start stop : Usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val) :
    core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      output {start,«end»:=stop} =
    ok (slice output start stop,fun s => output.setSlice! start.val s.val) := by
  simp [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    Array.to_slice,Slice.length,Slice.len,order,bound,output.property,
    Array.from_slice,Aeneas.Std.Array.setSlice!,slice]

theorem copy {W : Usize} (s : Slice U8) (bytes : Array U8 W)
    (width : s.length = W.val) :
    core.slice.Slice.copy_from_slice core.marker.CopyU8 s bytes.to_slice = ok bytes.to_slice := by
  simp [core.slice.Slice.copy_from_slice,Slice.len,Slice.length,
    Array.to_slice,bytes.property,width]
theorem slice_length {N : Usize} (output : Array U8 N) (start stop : Usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val) :
    (slice output start stop).length = stop.val-start.val := by
  simp only [slice,Slice.length,List.slice,List.length_take,List.length_drop,output.property]
  omega

theorem copy_range {N W : Usize} (output : Array U8 N) (start stop : Usize)
    (bytes : Array U8 W) (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (width : stop.val-start.val = W.val) :
    core.slice.Slice.copy_from_slice core.marker.CopyU8 (slice output start stop) bytes.to_slice =
      ok bytes.to_slice :=
  copy _ bytes ((slice_length output start stop order bound).trans width)

theorem prefix_index {N : Usize} (output : Array U8 N) (stop : Usize) (bound : stop.val ≤ N.val) :
    core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
      output {«end»:=stop} =
    ok (slice output 0#usize stop,fun s => output.setSlice! 0 s.val) := by
  simp [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    Array.to_slice,Slice.length,Slice.len,bound,output.property,
    Array.from_slice,Aeneas.Std.Array.setSlice!,slice]

theorem suffix_index {N : Usize} (output : Array U8 N) (start : Usize) (bound : start.val ≤ N.val) :
    core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
      output {start} =
    ok (slice output start N,fun s => output.setSlice! start.val s.val) := by
  simp [core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    Array.to_slice,Slice.length,Slice.len,bound,output.property,
    Array.from_slice,Aeneas.Std.Array.setSlice!,slice,List.slice,List.take_length,List.length_drop]
  apply Subtype.ext
  change output.val.drop start.val = (output.val.drop start.val).take (N.val-start.val)
  have len : (output.val.drop start.val).length = N.val-start.val := by simp [output.property]
  rw [←len,List.take_length]
#print axioms suffix_index

#print axioms slice_length
#print axioms copy_range
#print axioms prefix_index
#print axioms index_mut
#print axioms copy
end NBP_ArrayIndex
