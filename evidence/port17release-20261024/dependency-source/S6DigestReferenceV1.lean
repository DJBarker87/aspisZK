import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisS6DigestReference
abbrev M31 := U32
def M31.to_le_bytes (self : M31) : Result (Array Std.U8 4#usize) := do
  ok (core.num.U32.to_le_bytes self)



def encode_digest_canonical
  (digest : Array M31 8#usize) : Result (Array Std.U8 32#usize) := do
  let bytes := Array.repeat 32#usize 0#u8
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes
      { start := 0#usize, «end» := 4#usize }
  let m ← Array.index_usize digest 0#usize
  let a ← M31.to_le_bytes m
  let s1 ← lift (Array.to_slice a)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let bytes1 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes1
      { start := 4#usize, «end» := 8#usize }
  let m1 ← Array.index_usize digest 1#usize
  let a1 ← M31.to_le_bytes m1
  let s4 ← lift (Array.to_slice a1)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let bytes2 := index_mut_back1 s5
  let (s6, index_mut_back2) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes2
      { start := 8#usize, «end» := 12#usize }
  let m2 ← Array.index_usize digest 2#usize
  let a2 ← M31.to_le_bytes m2
  let s7 ← lift (Array.to_slice a2)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let bytes3 := index_mut_back2 s8
  let (s9, index_mut_back3) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes3
      { start := 12#usize, «end» := 16#usize }
  let m3 ← Array.index_usize digest 3#usize
  let a3 ← M31.to_le_bytes m3
  let s10 ← lift (Array.to_slice a3)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  let bytes4 := index_mut_back3 s11
  let (s12, index_mut_back4) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes4
      { start := 16#usize, «end» := 20#usize }
  let m4 ← Array.index_usize digest 4#usize
  let a4 ← M31.to_le_bytes m4
  let s13 ← lift (Array.to_slice a4)
  let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
  let bytes5 := index_mut_back4 s14
  let (s15, index_mut_back5) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes5
      { start := 20#usize, «end» := 24#usize }
  let m5 ← Array.index_usize digest 5#usize
  let a5 ← M31.to_le_bytes m5
  let s16 ← lift (Array.to_slice a5)
  let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
  let bytes6 := index_mut_back5 s17
  let (s18, index_mut_back6) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes6
      { start := 24#usize, «end» := 28#usize }
  let m6 ← Array.index_usize digest 6#usize
  let a6 ← M31.to_le_bytes m6
  let s19 ← lift (Array.to_slice a6)
  let s20 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s18 s19
  let bytes7 := index_mut_back6 s20
  let (s21, index_mut_back7) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) bytes7
      { start := 28#usize, «end» := 32#usize }
  let m7 ← Array.index_usize digest 7#usize
  let a7 ← M31.to_le_bytes m7
  let s22 ← lift (Array.to_slice a7)
  let s23 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s21 s22
  ok (index_mut_back7 s23)



#print axioms encode_digest_canonical
end AspisS6DigestReference
