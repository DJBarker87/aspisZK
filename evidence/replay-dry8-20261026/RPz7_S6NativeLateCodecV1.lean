import RPz7_S6NativeLateEncoderContentsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateCodec
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeLateDecoderSplit.Frames

theorem accepted_roundtrip (bytes : Slice U8) (statement : PoolV1PairLatePublicStatementV1)
    (output updated : Slice U8)
    (accepted : decode_pool_v1_pair_late_public_statement_boxed_v1 bytes=ok (core.result.Result.Ok statement))
    (size : output.length=1520)
    (encoded : encode_pool_v1_pair_late_public_statement_v1 statement output=ok (core.result.Result.Ok (),updated)) :
    updated.val=bytes.val := by
  obtain ⟨snapshot_validated,afterstate_validated,checked⟩ :=
    AspisS6NativeLateDecodeTotal.accepted_validity bytes statement accepted
  have graph := AspisS6NativeLateEncoderContents.encode_contents_spec statement output size
    snapshot_validated afterstate_validated checked
  rw [encoded,WP.spec_ok] at graph
  rcases graph with ⟨_,snapshot_initial,snapshot_updated,afterstate_output,snapshot_run,afterstate_run,_,layout⟩
  rcases AspisS6NativeLateDecodeTotal.accepted_frames bytes statement accepted with
    ⟨⟨raw,rawbytes,header⟩,⟨⟨snapshot_input,afterstate_input,snapshot_bytes,afterstate_bytes,snapshot_decode,afterstate_decode⟩,_⟩⟩
  have snapshot_contents := AspisS6NativeSnapshotCodec.accepted_roundtrip snapshot_input statement.live_snapshot
    snapshot_initial snapshot_updated snapshot_decode snapshot_run
  have afterstate_contents := AspisS6NativeAfterstateCodec.accepted_roundtrip afterstate_input statement.candidate_afterstate
    afterstate_output afterstate_decode afterstate_run
  have header_contents := AspisS6NativeLateHeaderLayout.header_prefix raw header
  rw [rawbytes] at header_contents
  rw [layout,header_contents,snapshot_contents,afterstate_contents,snapshot_bytes,afterstate_bytes]
  rw [AspisS6SliceFrame.take_append_slice bytes.val 32 832 (by decide),List.take_append_drop]

/-- Exact inverse for the original native mutable transition encoder. The sole
input premise is actual native decoder acceptance; output size is the API's
allocation requirement. Child/validator/encoder success are all derived. -/
theorem accepted_inverse (bytes : Slice U8) (statement : PoolV1PairLatePublicStatementV1)
    (accepted : decode_pool_v1_pair_late_public_statement_boxed_v1 bytes=ok (core.result.Result.Ok statement))
    (output : Slice U8) (size : output.length=1520) :
    ∃ updated : Slice U8,
      encode_pool_v1_pair_late_public_statement_v1 statement output=ok (core.result.Result.Ok (),updated) ∧
      updated.val=bytes.val := by
  obtain ⟨updated,encoded,_⟩ := AspisS6NativeLateEncodeAccepted.encode_from_decode bytes statement accepted output size
  exact ⟨updated,encoded,accepted_roundtrip bytes statement output updated accepted size encoded⟩

#print axioms accepted_roundtrip
#print axioms accepted_inverse
end AspisS6NativeLateCodec
