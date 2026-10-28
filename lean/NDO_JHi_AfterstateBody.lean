import NDO_JHi_AfterstateLoopAssociation
set_option autoImplicit false
namespace AspisR1.JHi_AfterstateBody
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

def decode (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  ⟨value.next_pair_index,value.next_root,value.next_frontier⟩

/-- Exact source byte action after successful validation, kept symbolic. -/
def body (afterstate : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : Result (Array U8 688#usize) := do
  let output := Array.repeat 688#usize 0#u8
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) output
      { «end» := 4#usize }
  let s1 ←
    lift (Array.to_slice
      aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let output1 := index_mut_back s2
  let output2 ←
    Array.update output1 4#usize
      aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
  let output3 ←
    Array.update output2 5#usize
      aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
  let output4 ←
    Array.update output3 6#usize
      aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  let output5 ← Array.update output4 7#usize 1#u8
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output5
      { start := 8#usize, «end» := 16#usize }
  let a ← lift (core.num.U64.to_le_bytes afterstate.next_pair_index)
  let s4 ← lift (Array.to_slice a)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let output6 := index_mut_back1 s5
  let (s6, index_mut_back2) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) output6
      { start := 16#usize, «end» := 48#usize }
  let a1 ←
    aspis_statement.atomic_statement.encode_digest_canonical
      afterstate.next_root
  let s7 ← lift (Array.to_slice a1)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let s9 ← lift (Array.to_slice afterstate.next_frontier)
  let i ← core.slice.Slice.iter s9
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter (Array
      aspis_core.field.M31 8#usize)) i
  let output7 := index_mut_back2 s8
  let output8 ←
    aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
      iter output7
  ok output8

theorem source (afterstate : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (validated : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate afterstate=ok (.Ok ())) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 afterstate=
    (body (decode afterstate) >>= fun out=>ok (core.result.Result.Ok out)) := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
  rw [validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [body,decode,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  congr 1
#print axioms source
end AspisR1.JHi_AfterstateBody
