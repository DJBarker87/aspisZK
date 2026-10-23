import S6NativeSnapshotDecodedLayoutV1
import S6NativeSnapshotEncodeSuccessV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotCodec
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeSnapshotEncoderGraph
open AspisS6NativeSnapshotDecoderFactored.Frames

theorem accepted_roundtrip (bytes : Slice U8) (snapshot : PoolV1PairLiveSnapshotV1)
    (output updated : Slice U8)
    (accepted : decode_pool_v1_pair_live_snapshot_v1 bytes=ok (core.result.Result.Ok snapshot))
    (encoded : encode_pool_v1_pair_live_snapshot_v1 snapshot output=ok (core.result.Result.Ok (),updated)) :
    updated.val=bytes.val := by
  have frames := AspisS6NativeSnapshotDecodeTotal.accepted_frames bytes snapshot accepted
  obtain ⟨decoded_format,decoded_run,layout⟩ := decoded_layout bytes snapshot frames
  have graph := encode_graph snapshot output
  rw [encoded,WP.spec_ok] at graph
  obtain ⟨format,format_run,contents⟩ := graph () rfl
  rw [format_run] at decoded_run
  cases decoded_run
  have hn : snapshot.frontier.val.length=20 := snapshot.frontier.property
  have fold_bytes := AspisS6NativeAfterstateEncoderReuse.Snapshot.frontier_fold_contents
    snapshot.frontier.val 0 (prepare snapshot decoded_format) (prefix_bytes snapshot decoded_format)
    (by simpa using prefix_length snapshot decoded_format)
    (by simpa only [hn,Nat.reduceMul] using prepare_contents snapshot decoded_format)
  exact contents.trans (fold_bytes.trans layout)

/-- Sole decode premise; the output buffer has the size required by the actual
mutable encoder. Validator and encoder success are derived. -/
theorem accepted_inverse (bytes : Slice U8) (snapshot : PoolV1PairLiveSnapshotV1)
    (accepted : decode_pool_v1_pair_live_snapshot_v1 bytes=ok (core.result.Result.Ok snapshot))
    (output : Slice U8) (size : output.length=800) :
    ∃ updated : Slice U8,
      encode_pool_v1_pair_live_snapshot_v1 snapshot output=ok (core.result.Result.Ok (),updated) ∧
      updated.val=bytes.val := by
  have frames := AspisS6NativeSnapshotDecodeTotal.accepted_frames bytes snapshot accepted
  rcases frames with ⟨_,_,_,_,_,_,_,validated⟩
  obtain ⟨⟨status,updated⟩,run,success⟩ := spec_imp_exists (encode_success snapshot output size validated)
  have encoded : encode_pool_v1_pair_live_snapshot_v1 snapshot output=ok (core.result.Result.Ok (),updated) := by
    change status=core.result.Result.Ok () at success
    rw [success] at run
    exact run
  exact ⟨updated,encoded,accepted_roundtrip bytes snapshot output updated accepted encoded⟩

#print axioms accepted_roundtrip
#print axioms accepted_inverse
end AspisS6NativeSnapshotCodec
