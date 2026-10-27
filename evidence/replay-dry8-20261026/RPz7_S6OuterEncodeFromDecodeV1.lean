import RPz7_S6OuterEncodeSuccessV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6OuterEncodeFromDecode
open AspisS6OuterCarrierBridge AspisS6OuterNativeOps
open AspisR1TerminalDecoder.pool_v1.pair_forest_terminal

theorem late_ready_from_decode (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok statement))
    (common : PoolV1PairForestTerminalCommonV1)
    (common_run : PoolV1PairForestTerminalStatementV1.common statement=ok common) :
    AspisS6OuterEncodeSuccess.late_ready (fromPoolV1PairLatePublicStatementV1 common.lane_transition) := by
  intro output size
  obtain ⟨reached,updated,reached_run,run,_⟩ :=
    AspisS6OuterAcceptedCallees.late_from_decode bytes statement accepted output size
  rw [common_run] at reached_run
  cases reached_run
  have frame := AspisS6OuterNativeTotalCallees.late_spec
    (fromPoolV1PairLatePublicStatementV1 common.lane_transition) output
  rw [run,WP.spec_ok] at frame
  exact ⟨updated,run,frame.trans size⟩

/-- Concrete outer encoding cannot return a format error after actual outer
native decoder acceptance. All child readiness premises are discharged here. -/
theorem encode_success (bytes : Slice U8) (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : decode_pool_v1_pair_forest_terminal_statement_v1 bytes=ok (.Ok statement)) :
    ∃ encoded : Array U8 1880#usize, AspisS6OuterNativeInstalled.encode statement=ok (.Ok encoded) := by
  have valid := AspisS6OuterAcceptedCallees.validate_from_decode bytes statement accepted
  have pay := AspisS6OuterAcceptedCallees.payment_from_decode bytes statement accepted
  cases statement with
  | PrivateTransfer common payload =>
    have late := late_ready_from_decode bytes (.PrivateTransfer common payload) accepted common rfl
    obtain ⟨payment,payment_run,_⟩ := pay
    have good := AspisS6OuterEncodeSuccess.private_success
      (fromPoolV1PairForestTerminalCommonV1 common) (fromPoolV1PrivateTransferPublicV1 payload)
      valid late ⟨payment,payment_run⟩
    obtain ⟨result,run,encoded,success⟩ := spec_imp_exists good
    cases success
    unfold AspisS6OuterNativeInstalled.encode
    rw [show fromPoolV1PairForestTerminalStatementV1 (.PrivateTransfer common payload)=
      .PrivateTransfer (fromPoolV1PairForestTerminalCommonV1 common) (fromPoolV1PrivateTransferPublicV1 payload) from rfl,run]
    exact ⟨encoded,rfl⟩
  | Withdrawal common payload =>
    have late := late_ready_from_decode bytes (.Withdrawal common payload) accepted common rfl
    obtain ⟨payment,payment_run,_⟩ := pay
    have good := AspisS6OuterEncodeSuccess.withdrawal_success
      (fromPoolV1PairForestTerminalCommonV1 common) (fromPoolV1WithdrawalPublicV1 payload)
      valid late ⟨payment,payment_run⟩
    obtain ⟨result,run,encoded,success⟩ := spec_imp_exists good
    cases success
    unfold AspisS6OuterNativeInstalled.encode
    rw [show fromPoolV1PairForestTerminalStatementV1 (.Withdrawal common payload)=
      .Withdrawal (fromPoolV1PairForestTerminalCommonV1 common) (fromPoolV1WithdrawalPublicV1 payload) from rfl,run]
    exact ⟨encoded,rfl⟩

#print axioms late_ready_from_decode
#print axioms encode_success
end AspisS6OuterEncodeFromDecode
