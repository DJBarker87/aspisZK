import RPz7_S6NativeLateAcceptedFramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeLateDecodeTotal
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeLateDecoderSplit.Frames

theorem accepted_validity (bytes : Slice U8) (statement : PoolV1PairLatePublicStatementV1)
    (accepted : decode_pool_v1_pair_late_public_statement_boxed_v1 bytes=ok (core.result.Result.Ok statement)) :
    validate_pool_v1_pair_live_snapshot_v1 statement.live_snapshot=ok (core.result.Result.Ok ()) ∧
    pool_v1.pair_terminal.validate_verified_afterstate statement.candidate_afterstate=ok (core.result.Result.Ok ()) ∧
    U64.checked_add statement.live_snapshot.next_pair_index 1#u64=some statement.candidate_afterstate.next_pair_index := by
  rcases accepted_frames bytes statement accepted with
    ⟨_,⟨⟨snapshot_input,afterstate_input,_,_,snapshot_accepted,afterstate_accepted⟩,checked⟩⟩
  rcases AspisS6NativeSnapshotDecodeTotal.accepted_frames snapshot_input statement.live_snapshot snapshot_accepted with
    ⟨_,_,_,_,_,_,_,snapshot_validated⟩
  rcases AspisS6NativeAfterstateCodec.accepted_frames afterstate_input statement.candidate_afterstate afterstate_accepted with
    ⟨_,_,_,_,afterstate_validated⟩
  exact ⟨snapshot_validated,afterstate_validated,checked⟩

#print axioms accepted_validity
end AspisS6NativeLateDecodeTotal
