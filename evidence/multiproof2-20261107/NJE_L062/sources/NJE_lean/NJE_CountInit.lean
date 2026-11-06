import NJA_CountBody

set_option autoImplicit false
namespace NJE_CountInit
open Aeneas Aeneas.Std Result

def source (indices : Slice U32) : Result (Array U32 16#usize) := do
 let level := Array.repeat 16#usize 0#u32
 let (part,back) ← core.array.Array.index_mut
   (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
   level {«end»:=Slice.len indices}
 let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU32 part indices
 ok (back copied)

def value (indices : Slice U32) (bound : indices.val.length≤16) : Array U32 16#usize :=
 ⟨indices.val++List.replicate (16-indices.val.length) 0#u32,by
   simp only [List.length_append,List.length_replicate]
   change indices.val.length+(16-indices.val.length)=16
   omega⟩

#print Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
#print Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut
#print Aeneas.Std.Array.from_slice
#print List.setSlice!

theorem result (indices : Slice U32) (bound : indices.val.length≤16) :
    source indices=ok (value indices bound) := by
 simp [source,core.array.Array.index_mut,core.ops.index.IndexMutSlice,
   core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeToUsizeSlice,
   core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
   core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
   core.slice.Slice.copy_from_slice,Array.repeat,Array.to_slice,Array.from_slice,value,bound,Slice.len,List.setSlice!]

#print result
#print axioms result
end NJE_CountInit
