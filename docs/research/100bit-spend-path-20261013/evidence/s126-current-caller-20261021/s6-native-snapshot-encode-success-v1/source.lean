import S6NativeSnapshotEncoderGraphV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotEncoderGraph
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := by exact a.property

theorem encode_success (snapshot : PoolV1PairLiveSnapshotV1) (output : Slice U8)
    (size : output.length=800)
    (validated : validate_pool_v1_pair_live_snapshot_v1 snapshot=ok (core.result.Result.Ok ())) :
    encode_pool_v1_pair_live_snapshot_v1 snapshot output
      ⦃ result => result.1=core.result.Result.Ok () ⦄ := by
  unfold encode_pool_v1_pair_live_snapshot_v1 POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    core.slice.Slice.iter core.iter.traits.iterator.Iterator.enumerate.trait_default
    core.iter.traits.iterator.Iterator.enumerate.default
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    AspisS6NativeSliceFrame.setSlice_length,List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> try scalar_tac)
  all_goals step*
  all_goals simp_all

#print axioms encode_success
end AspisS6NativeSnapshotEncoderGraph
