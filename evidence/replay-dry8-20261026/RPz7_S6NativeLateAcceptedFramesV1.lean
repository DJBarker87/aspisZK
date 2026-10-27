import RPz7_S6NativeLateDecodedFramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateDecodeTotal
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeLateDecoderSplit
open AspisS6NativeLateDecoderSplit.Frames

theorem accepted_frames (bytes : Slice U8) (statement : PoolV1PairLatePublicStatementV1)
    (accepted : decode_pool_v1_pair_late_public_statement_boxed_v1 bytes=ok (core.result.Result.Ok statement)) :
    full_frame bytes statement := by
  have frames := decode_frames bytes
  rw [decode_source bytes,accepted,WP.spec_ok] at frames
  exact frames statement rfl

#print axioms accepted_frames
end AspisS6NativeLateDecodeTotal
