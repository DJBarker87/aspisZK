import RPz7_S2K_AfterstateLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.AfterstatePrefix
open AspisR1TerminalDecoder
abbrev Afterstate := pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

def fields (afterstate : Afterstate) (output : Array U8 688#usize) :
    Result (LoopStep.Iter × Array U8 688#usize) := do
    let (s, index_mut_back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output { «end» := 4#usize }
    let s1 ← lift (Array.to_slice pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC)
    let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
    let output1 := index_mut_back s2
    let output2 ← Array.update output1 4#usize pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
    let output3 ← Array.update output2 5#usize pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
    let output4 ← Array.update output3 6#usize pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
    let output5 ← Array.update output4 7#usize 1#u8
    let (s3, index_mut_back1) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5 { start := 8#usize, «end» := 16#usize }
    let a ← lift (core.num.U64.to_le_bytes afterstate.next_pair_index)
    let s4 ← lift (Array.to_slice a)
    let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
    let output6 := index_mut_back1 s5
    let (s6, index_mut_back2) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output6 { start := 16#usize, «end» := 48#usize }
    let a1 ← atomic_statement.encode_digest_canonical afterstate.next_root
    let s7 ← lift (Array.to_slice a1)
    let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
    let s9 ← lift (Array.to_slice afterstate.next_frontier)
    let i ← core.slice.Slice.iter s9
    let iter ← core.iter.traits.iterator.Iterator.enumerate.trait_default (core.iter.traits.iterator.IteratorSliceIter (Array aspis_core.field.M31 8#usize)) i
    let output7 := index_mut_back2 s8
    ok (iter, output7)

theorem total (afterstate : Afterstate) (output : Array U8 688#usize) :
    ∃ out, fields afterstate output = ok (Iterator.cursor afterstate.next_frontier 0#usize,out) := by
  obtain ⟨root,encoded⟩ := DigestTotal.total afterstate.next_root
  unfold fields
  simp only [encoded,bind_tc_ok,lift]
  simp [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    Array.to_slice, Array.from_slice, core.slice.Slice.copy_from_slice,
    Slice.length, Slice.len, Array.update, output.property, List.slice,
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, Iterator.cursor]

#print axioms total
end AspisR1.S2K.AfterstatePrefix
