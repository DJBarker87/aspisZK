import NBK_LiveBytes
import JFt_SnapshotConstants
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NBK_LivePrepare
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_tree_profile
abbrev Snapshot := PoolV1PairLiveSnapshotV1

def run {T : Type} (snapshot : Snapshot) (output : Slice U8)
    (k : LoopStep.Iter → Slice U8 → Result T) : Result T := do
      let (s, index_mut_back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) output { «end» := 8#usize }
      let s1 ← lift (Array.to_slice pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let output2 := index_mut_back s2
      let output3 ← Slice.update output2 8#usize pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
      let (s3, index_mut_back1) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output3 { start := 16#usize, «end» := 48#usize }
      let a ← pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
      let output4 := index_mut_back1 s5
      let (s6, index_mut_back2) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output4 { start := 48#usize, «end» := 80#usize }
      let s7 ← lift (Array.to_slice snapshot.pool)
      let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
      let output5 := index_mut_back2 s8
      let (s9, index_mut_back3) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output5 { start := 80#usize, «end» := 112#usize }
      let s10 ← lift (Array.to_slice snapshot.deployment_domain)
      let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
      let output6 := index_mut_back3 s11
      let (s12, index_mut_back4) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output6 { start := 112#usize, «end» := 120#usize }
      let a1 ← lift (core.num.U64.to_le_bytes snapshot.sequence)
      let s13 ← lift (Array.to_slice a1)
      let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
      let output7 := index_mut_back4 s14
      let (s15, index_mut_back5) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output7 { start := 120#usize, «end» := 128#usize }
      let a2 ← lift (core.num.U64.to_le_bytes snapshot.next_pair_index)
      let s16 ← lift (Array.to_slice a2)
      let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
      let output8 := index_mut_back5 s17
      let (s18, index_mut_back6) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output8 { start := 128#usize, «end» := 160#usize }
      let a3 ← atomic_statement.encode_digest_canonical snapshot.current_root
      let s19 ← lift (Array.to_slice a3)
      let s20 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s18 s19
      let s21 ← lift (Array.to_slice snapshot.frontier)
      let i1 ← core.slice.Slice.iter s21
      let iter ← core.iter.traits.iterator.Iterator.enumerate.trait_default (core.iter.traits.iterator.IteratorSliceIter (Array aspis_core.field.M31 8#usize)) i1
      let output9 := index_mut_back6 s20
      k iter output9

def value (a : Snapshot) (output : Slice U8) : Slice U8 :=
  ⟨((((((((output.val.setSlice! 0 POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val).set
      8 POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION).setSlice!
      16 AspisR1.JFt_SnapshotConstants.formatArray.val).setSlice!
      48 a.pool.val).setSlice! 80 a.deployment_domain.val).setSlice!
      112 (core.num.U64.to_le_bytes a.sequence).val).setSlice!
      120 (core.num.U64.to_le_bytes a.next_pair_index).val).setSlice!
      128 (DigestBytes.bytes a.current_root).val), by
        simpa only [List.length_setSlice!,List.length_set] using output.property⟩

theorem exact {T : Type} (a : Snapshot) (output : Slice U8)
    (size : output.length = 800) (k : LoopStep.Iter → Slice U8 → Result T) :
    run a output k = k (Iterator.cursor a.frontier 0#usize) (value a output) := by
  have len : output.val.length = 800 := size
  unfold run
  simp only [DigestBytes.exact,AspisR1.JFt_SnapshotConstants.format_call,bind_tc_ok,lift]
  simp [core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    Array.to_slice, core.slice.Slice.copy_from_slice,
    Slice.length, Slice.len, Slice.update, len, List.slice,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, Iterator.cursor,value]

#print axioms exact
end NBK_LivePrepare
