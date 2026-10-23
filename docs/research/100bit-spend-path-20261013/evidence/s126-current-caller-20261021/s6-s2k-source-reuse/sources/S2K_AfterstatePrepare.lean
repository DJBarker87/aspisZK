import S2K_AfterstateBytes

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.AfterstatePrepare
open AspisR1TerminalDecoder
open pool_v1.pair_terminal
abbrev Afterstate := PoolV1PairVerifiedAfterstateV1

def run {T : Type} (afterstate : Afterstate) (output : Array U8 688#usize)
    (k : LoopStep.Iter → Array U8 688#usize → Result T) : Result T := do
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
    k iter output7

def value (a : Afterstate) (output : Array U8 688#usize) : Array U8 688#usize :=
  ⟨(((((((output.val.setSlice! 0 POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.val).set
      4 POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION).set
      5 pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION).set
      6 pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION).set 7 1#u8).setSlice!
      8 (core.num.U64.to_le_bytes a.next_pair_index).val).setSlice!
      16 (DigestBytes.bytes a.next_root).val), by
        simp only [List.length_setSlice!,List.length_set,output.property]⟩

theorem exact {T : Type} (a : Afterstate) (output : Array U8 688#usize)
    (k : LoopStep.Iter → Array U8 688#usize → Result T) :
    run a output k = k (Iterator.cursor a.next_frontier 0#usize) (value a output) := by
  unfold run
  simp only [DigestBytes.exact,bind_tc_ok,lift]
  simp [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    Array.to_slice, Array.from_slice, core.slice.Slice.copy_from_slice,
    Slice.length, Slice.len, Array.update, output.property, List.slice,
    pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, Iterator.cursor,value]

#print axioms exact
end AspisR1.S2K.AfterstatePrepare
