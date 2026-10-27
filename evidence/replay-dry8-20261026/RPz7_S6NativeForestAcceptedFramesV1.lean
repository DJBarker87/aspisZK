import RPz7_S6NativeForestDecodedFramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeForestDecode
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

theorem accepted_frames (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (core.result.Result.Ok statement)) :
    full_frame bytes statement := by
  have frames := decode_frames bytes
  rw [accepted,WP.spec_ok] at frames
  exact frames statement rfl

#print axioms accepted_frames
end AspisS6NativeForestDecode
