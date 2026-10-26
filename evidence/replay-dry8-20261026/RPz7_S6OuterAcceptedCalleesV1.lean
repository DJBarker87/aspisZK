import RPz7_S6OuterNativeInstalledV1
import RPz7_S6NativeForestAcceptedFramesV1
import RPz7_S6NativeLateCodecV1
import RPz7_S6NativePaymentRoundtripV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6OuterAcceptedCallees
open AspisR1TerminalDecoder AspisS6OuterCarrierBridge AspisS6OuterNativeOps
open pool_v1.pair_forest_terminal

/-- Actual installed payment call succeeds and reproduces the reached suffix.
No independent child success or canonicality premise is supplied. -/
def payment (bytes : Slice U8) : PoolV1PairForestTerminalStatementV1 → Prop
  | .PrivateTransfer _ value => ∃ encoded : Array U8 216#usize,
      nativeOps.transfer (fromPoolV1PrivateTransferPublicV1 value)=ok (.Ok encoded) ∧
      encoded.val=bytes.val.drop 1664
  | .Withdrawal _ value => ∃ encoded : Array U8 216#usize,
      nativeOps.withdrawal (fromPoolV1WithdrawalPublicV1 value)=ok (.Ok encoded) ∧
      encoded.val=bytes.val.drop 1664

theorem payment_from_decode (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok statement)) :
    payment bytes statement := by
  have frame := (AspisS6NativeForestDecode.accepted_frames bytes statement accepted).2.2.1
  cases statement with
  | PrivateTransfer common value =>
    obtain ⟨input,input_bytes,decoded⟩ := frame
    obtain ⟨encoded,contents,run⟩ := AspisS6NativePaymentContents.transfer_accepted_inverse input value decoded
    refine ⟨encoded,?_,contents.trans input_bytes⟩
    rw [transfer_call,run]
    rfl
  | Withdrawal common value =>
    obtain ⟨input,input_bytes,decoded⟩ := frame
    obtain ⟨encoded,contents,run⟩ := AspisS6NativePaymentContents.withdrawal_accepted_inverse input value decoded
    refine ⟨encoded,?_,contents.trans input_bytes⟩
    rw [withdrawal_call,run]
    rfl

theorem validate_from_decode (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok statement)) :
    nativeOps.validate (fromPoolV1PairForestTerminalStatementV1 statement)=ok (.Ok ()) := by
  rw [validate_call,(AspisS6NativeForestDecode.accepted_frames bytes statement accepted).2.2.2]
  rfl

/-- The reached common selector and installed mutable transition call are
connected to the same accepted outer statement, retaining its caller buffer. -/
theorem late_from_decode (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok statement))
    (output : Slice U8) (size : output.length=1520) :
    ∃ common updated,
      PoolV1PairForestTerminalStatementV1.common statement=ok common ∧
      nativeOps.late (fromPoolV1PairLatePublicStatementV1 common.lane_transition) output=
        ok (.Ok (),updated) ∧ updated.val=List.slice 144 1664 bytes.val := by
  obtain ⟨common,common_run,fields⟩ :=
    (AspisS6NativeForestDecode.accepted_frames bytes statement accepted).2.1
  obtain ⟨input,input_bytes,decoded⟩ := fields.2.2.2.2.2.2
  obtain ⟨updated,run,contents⟩ := AspisS6NativeLateCodec.accepted_inverse input common.lane_transition decoded output size
  refine ⟨common,updated,common_run,?_,contents.trans input_bytes⟩
  rw [late_call,run]
  rfl

#print axioms payment_from_decode
#print axioms validate_from_decode
#print axioms late_from_decode
end AspisS6OuterAcceptedCallees
