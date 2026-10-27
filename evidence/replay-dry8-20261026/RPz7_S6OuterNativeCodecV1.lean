import RPz7_S6OuterEncoderContentsV1
import RPz7_S6OuterAcceptedByteJoinV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6OuterNativeCodec
open AspisS6OuterCarrierBridge AspisS6OuterNativeOps
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal

/-- Complete outer1880 inverse at the concrete installed original encoder cut.
The only input premise is original native decoder acceptance. -/
theorem accepted_inverse (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok statement)) :
    ∃ encoded : Array U8 1880#usize,
      AspisS6OuterNativeInstalled.encode statement=ok (.Ok encoded) ∧ encoded.val=bytes.val := by
  have valid := AspisS6OuterAcceptedCallees.validate_from_decode bytes statement accepted
  have pay := AspisS6OuterAcceptedCallees.payment_from_decode bytes statement accepted
  cases statement with
  | PrivateTransfer common payload =>
    have late := AspisS6OuterEncodeFromDecode.late_ready_from_decode bytes (.PrivateTransfer common payload) accepted common rfl
    obtain ⟨payment,payment_run,_⟩ := pay
    have good := AspisS6OuterEncoderContents.private_contents
      (fromPoolV1PairForestTerminalCommonV1 common) (fromPoolV1PrivateTransferPublicV1 payload)
      valid late ⟨payment,payment_run⟩
    obtain ⟨result,run,encoded,initial,updated,payment,success,size,len,late_run,pay_run,layout⟩ := spec_imp_exists good
    cases success
    simp only [AspisS6OuterEncoderContents.common_prefix] at layout
    have common_bytes := AspisS6OuterAcceptedByteJoin.common_contents bytes (.PrivateTransfer common payload) accepted common rfl
    simp only [AspisS6NativeForestDecode.statement_tag] at common_bytes
    have late_bytes := AspisS6OuterAcceptedByteJoin.late_contents bytes (.PrivateTransfer common payload) accepted common rfl initial updated size late_run
    have payment_bytes := AspisS6OuterAcceptedByteJoin.transfer_contents bytes common payload accepted payment pay_run
    refine ⟨encoded,?_,?_⟩
    · unfold AspisS6OuterNativeInstalled.encode
      rw [show fromPoolV1PairForestTerminalStatementV1 (.PrivateTransfer common payload)=
        .PrivateTransfer (fromPoolV1PairForestTerminalCommonV1 common) (fromPoolV1PrivateTransferPublicV1 payload) from rfl,run]
      rfl
    · rw [layout,common_bytes,late_bytes,payment_bytes]
      rw [AspisS6SliceFrame.take_append_slice bytes.val 144 1664 (by decide),List.take_append_drop]
  | Withdrawal common payload =>
    have late := AspisS6OuterEncodeFromDecode.late_ready_from_decode bytes (.Withdrawal common payload) accepted common rfl
    obtain ⟨payment,payment_run,_⟩ := pay
    have good := AspisS6OuterEncoderContents.withdrawal_contents
      (fromPoolV1PairForestTerminalCommonV1 common) (fromPoolV1WithdrawalPublicV1 payload)
      valid late ⟨payment,payment_run⟩
    obtain ⟨result,run,encoded,initial,updated,payment,success,size,len,late_run,pay_run,layout⟩ := spec_imp_exists good
    cases success
    simp only [AspisS6OuterEncoderContents.common_prefix] at layout
    have common_bytes := AspisS6OuterAcceptedByteJoin.common_contents bytes (.Withdrawal common payload) accepted common rfl
    simp only [AspisS6NativeForestDecode.statement_tag] at common_bytes
    have late_bytes := AspisS6OuterAcceptedByteJoin.late_contents bytes (.Withdrawal common payload) accepted common rfl initial updated size late_run
    have payment_bytes := AspisS6OuterAcceptedByteJoin.withdrawal_contents bytes common payload accepted payment pay_run
    refine ⟨encoded,?_,?_⟩
    · unfold AspisS6OuterNativeInstalled.encode
      rw [show fromPoolV1PairForestTerminalStatementV1 (.Withdrawal common payload)=
        .Withdrawal (fromPoolV1PairForestTerminalCommonV1 common) (fromPoolV1WithdrawalPublicV1 payload) from rfl,run]
      rfl
    · rw [layout,common_bytes,late_bytes,payment_bytes]
      rw [AspisS6SliceFrame.take_append_slice bytes.val 144 1664 (by decide),List.take_append_drop]

theorem accepted_roundtrip (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (encoded : Array U8 1880#usize)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok statement))
    (encoded_actual : AspisS6OuterNativeInstalled.encode statement=ok (.Ok encoded)) :
    encoded.val=bytes.val := by
  obtain ⟨correct,run,contents⟩ := accepted_inverse bytes statement accepted
  rw [encoded_actual] at run
  cases run
  exact contents

#print axioms accepted_inverse
#print axioms accepted_roundtrip
end AspisS6OuterNativeCodec
