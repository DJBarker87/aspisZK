import S6NativeSnapshotAcceptedFramesV1
import S6NativeDigestByteContentsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotEncoderGraph
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def prepare (snapshot : PoolV1PairLiveSnapshotV1) (format : Array U8 32#usize) : Slice U8 :=
  ⟨((((((((List.replicate 800 0#u8).setSlice! 0 POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val).set 8 POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION).setSlice! 16 format.val).setSlice! 48 snapshot.pool.val).setSlice! 80 snapshot.deployment_domain.val).setSlice! 112 (core.num.U64.to_le_bytes snapshot.sequence).val).setSlice! 120 (core.num.U64.to_le_bytes snapshot.next_pair_index).val).setSlice! 128 (AspisS6SourceCodec.DigestContents.chunks snapshot.current_root), by
    simp only [AspisS6SliceFrame.setSlice_length,List.length_set,List.length_replicate]
    scalar_tac⟩

@[step] theorem frontier_graph (rows : AspisS6NativeSnapshotLoop.Rows) (output : Slice U8)
    (size : output.length=800) :
    encode_pool_v1_pair_live_snapshot_v1_loop
      {iter:={slice:=Array.to_slice rows,i:=0},count:=0#usize} output
      ⦃ result => result.val=(AspisS6NativeSnapshotLoop.fold rows.val 0 output).val ⦄ := by
  rw [AspisS6NativeSnapshotLoop.loop_exact rows 0#usize (by decide) output size,WP.spec_ok]
  rfl

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := by
  exact a.property

@[step] theorem encode_graph (snapshot : PoolV1PairLiveSnapshotV1) (output : Slice U8) :
    encode_pool_v1_pair_live_snapshot_v1 snapshot output
      ⦃ result => ∀ unit, result.1=core.result.Result.Ok unit →
        ∃ format : Array U8 32#usize,
          POOL_V1_PAIR_TREE_FORMAT_BINDING=ok format ∧
          result.2.val=(AspisS6NativeSnapshotLoop.fold snapshot.frontier.val 0 (prepare snapshot format)).val ⦄ := by
  unfold encode_pool_v1_pair_live_snapshot_v1 POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    core.slice.Slice.iter core.iter.traits.iterator.Iterator.enumerate.trait_default
    core.iter.traits.iterator.Iterator.enumerate.default
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    AspisS6NativeSliceFrame.setSlice_length,List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> try scalar_tac)
  all_goals step*
  all_goals (simp_all [prepare])

#print axioms frontier_graph
#print axioms encode_graph
end AspisS6NativeSnapshotEncoderGraph
