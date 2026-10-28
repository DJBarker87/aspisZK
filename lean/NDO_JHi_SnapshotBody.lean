import NDO_JHi_SnapshotLoopAssociation
set_option autoImplicit false
namespace AspisR1.JHi_SnapshotBody
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

def decode (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  ⟨value.pool,value.deployment_domain,value.sequence,value.next_pair_index,value.current_root,value.frontier⟩

/-- Exact source byte action after successful validation, kept symbolic. -/
def body (snapshot : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) (output : Slice U8) : Result (Slice U8) := do
  let output1 ← core.slice.Slice.fill core.clone.CloneU8 output 0#u8
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) output1
      { «end» := 8#usize }
  let s1 ←
    lift (Array.to_slice
      aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let output2 := index_mut_back s2
  let output3 ←
    Slice.update output2 8#usize
      aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
  let (s3, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output3
      { start := 16#usize, «end» := 48#usize }
  let a ←
    aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
  let s4 ← lift (Array.to_slice a)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let output4 := index_mut_back1 s5
  let (s6, index_mut_back2) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output4
      { start := 48#usize, «end» := 80#usize }
  let s7 ← lift (Array.to_slice snapshot.pool)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let output5 := index_mut_back2 s8
  let (s9, index_mut_back3) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output5
      { start := 80#usize, «end» := 112#usize }
  let s10 ← lift (Array.to_slice snapshot.deployment_domain)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  let output6 := index_mut_back3 s11
  let (s12, index_mut_back4) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output6
      { start := 112#usize, «end» := 120#usize }
  let a1 ← lift (core.num.U64.to_le_bytes snapshot.sequence)
  let s13 ← lift (Array.to_slice a1)
  let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
  let output7 := index_mut_back4 s14
  let (s15, index_mut_back5) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output7
      { start := 120#usize, «end» := 128#usize }
  let a2 ← lift (core.num.U64.to_le_bytes snapshot.next_pair_index)
  let s16 ← lift (Array.to_slice a2)
  let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
  let output8 := index_mut_back5 s17
  let (s18, index_mut_back6) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output8
      { start := 128#usize, «end» := 160#usize }
  let a3 ←
    aspis_statement.atomic_statement.encode_digest_canonical
      snapshot.current_root
  let s19 ← lift (Array.to_slice a3)
  let s20 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s18 s19
  let s21 ← lift (Array.to_slice snapshot.frontier)
  let i1 ← core.slice.Slice.iter s21
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter (Array
      aspis_core.field.M31 8#usize)) i1
  let output9 := index_mut_back6 s20
  let output10 ←
    aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop
      iter output9
  ok output10

theorem source (snapshot : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) (output : Slice U8)
    (size : Slice.len output=800#usize)
    (validated : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 snapshot=ok (.Ok ())) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 snapshot output=
    (body (decode snapshot) output >>= fun out=>ok (core.result.Result.Ok (),out)) := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1
  rw [size]
  simp only [aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,show (800#usize !=800#usize)=false from rfl,Bool.false_eq_true,↓reduceIte]
  rw [validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [body,decode,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  congr 1
#print axioms source
end AspisR1.JHi_SnapshotBody
