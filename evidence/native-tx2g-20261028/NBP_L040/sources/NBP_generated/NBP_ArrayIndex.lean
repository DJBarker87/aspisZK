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
#print axioms index_mut
#print axioms copy
end NBP_ArrayIndex
