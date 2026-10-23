import S6NativeLateAcceptedFramesV1
import S6NativeLateChildEncodeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateEncodeAccepted
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeLateDecoderSplit.Frames

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := a.property

theorem encode_spec (bytes : Slice U8) (statement : PoolV1PairLatePublicStatementV1)
    (accepted : decode_pool_v1_pair_late_public_statement_boxed_v1 bytes=ok (core.result.Result.Ok statement))
    (output : Slice U8) (size : output.length=1520) :
    encode_pool_v1_pair_late_public_statement_v1 statement output
      ⦃ result => result.1=core.result.Result.Ok () ∧ result.2.length=1520 ⦄ := by
  have frames := AspisS6NativeLateDecodeTotal.accepted_frames bytes statement accepted
  rcases frames with ⟨header,⟨⟨snapshot_input,afterstate_input,snapshot_bytes,afterstate_bytes,snapshot_accepted,afterstate_accepted⟩,checked⟩⟩
  have snapshot_frames := AspisS6NativeSnapshotDecodeTotal.accepted_frames snapshot_input statement.live_snapshot snapshot_accepted
  rcases snapshot_frames with ⟨_,_,_,_,_,_,_,snapshot_validated⟩
  have afterstate_frames := AspisS6NativeAfterstateCodec.accepted_frames afterstate_input statement.candidate_afterstate afterstate_accepted
  rcases afterstate_frames with ⟨_,_,_,_,afterstate_validated⟩
  unfold encode_pool_v1_pair_late_public_statement_v1
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
    core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEq.ne.trait_default
  step*
  all_goals (simp_all only [array_slice_length,Slice.length,Slice.set,Slice.setAtNat,
    AspisS6NativeSliceFrame.setSlice_length,List.length_set,AspisS6SliceFrame.setSlice_length,List.length_replicate] <;> first | scalar_tac | step*)
  all_goals (simp_all [core.result.Result.Insts.CoreOpsTry.branch])

#print axioms encode_spec
end AspisS6NativeLateEncodeAccepted
