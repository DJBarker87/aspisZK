import NBN_EncoderBytes
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NBN_EncoderContents
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult
open AspisS6OuterNativeOps AspisS6OuterCarrierBridge
open pool_v1.pair_forest_terminal

theorem private_contents (c : PoolV1PairForestTerminalCommonV1)
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 (.PrivateTransfer c p) = ok (.Ok ())) :
    ∃ pay : Array U8 216#usize,
      payment (.PrivateTransfer c p) = ok (.Ok pay) ∧
      AspisS6OuterNativeInstalled.encode (.PrivateTransfer c p) =
        ok (.Ok (NBN_EncoderBytes.bytes (.PrivateTransfer c p) pay)) := by
  have good := AspisS6OuterEncoderContents.private_contents
    (fromPoolV1PairForestTerminalCommonV1 c) (fromPoolV1PrivateTransferPublicV1 p)
    (NBN_EncoderDomains.validator (.PrivateTransfer c p) valid) (NBN_EncoderDomains.late (.PrivateTransfer c p) valid)
    (NBN_EncoderDomains.transfer c p valid)
  obtain ⟨r,run,encoded,initial,updated,pay,success,size,len,late_run,pay_run,layout⟩ := WP.spec_imp_exists good
  cases success
  have late_call := AspisS6OuterNativeOps.late_call c.lane_transition initial
  have ready := (NBN_LateInvariant.statement_ready (.PrivateTransfer c p) valid initial size).1
  change pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 c.lane_transition initial =
    ok (.Ok (),NBN_LateTail.value c.lane_transition NBN_LateResult.header) at ready
  change nativeOps.late (fromPoolV1PairLatePublicStatementV1 c.lane_transition) initial = ok (.Ok (),updated) at late_run
  rw [ready] at late_call
  rw [late_call] at late_run
  change ok (.Ok (),NBN_LateTail.value c.lane_transition NBN_LateResult.header) = ok (.Ok (),updated) at late_run
  have same : NBN_LateTail.value c.lane_transition NBN_LateResult.header = updated :=
    congrArg Prod.snd (Result.ok.inj late_run)
  have pay_call := AspisS6OuterNativeOps.transfer_return p
  rw [pay_run] at pay_call
  change ok (.Ok pay) = pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p at pay_call
  have bytes_equal : encoded = NBN_EncoderBytes.bytes (.PrivateTransfer c p) pay := by
    apply Subtype.ext
    rw [layout,← same]
    rfl
  refine ⟨pay,pay_call.symm,?_⟩
  unfold AspisS6OuterNativeInstalled.encode
  change resultMap _ (AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 nativeOps
    (.PrivateTransfer (fromPoolV1PairForestTerminalCommonV1 c) (fromPoolV1PrivateTransferPublicV1 p))) = _
  rw [run,bytes_equal]
  rfl

theorem withdrawal_contents (c : PoolV1PairForestTerminalCommonV1)
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 (.Withdrawal c p) = ok (.Ok ())) :
    ∃ pay : Array U8 216#usize,
      payment (.Withdrawal c p) = ok (.Ok pay) ∧
      AspisS6OuterNativeInstalled.encode (.Withdrawal c p) =
        ok (.Ok (NBN_EncoderBytes.bytes (.Withdrawal c p) pay)) := by
  have good := AspisS6OuterEncoderContents.withdrawal_contents
    (fromPoolV1PairForestTerminalCommonV1 c) (fromPoolV1WithdrawalPublicV1 p)
    (NBN_EncoderDomains.validator (.Withdrawal c p) valid) (NBN_EncoderDomains.late (.Withdrawal c p) valid)
    (NBN_EncoderDomains.withdrawal c p valid)
  obtain ⟨r,run,encoded,initial,updated,pay,success,size,len,late_run,pay_run,layout⟩ := WP.spec_imp_exists good
  cases success
  have late_call := AspisS6OuterNativeOps.late_call c.lane_transition initial
  have ready := (NBN_LateInvariant.statement_ready (.Withdrawal c p) valid initial size).1
  change pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 c.lane_transition initial =
    ok (.Ok (),NBN_LateTail.value c.lane_transition NBN_LateResult.header) at ready
  change nativeOps.late (fromPoolV1PairLatePublicStatementV1 c.lane_transition) initial = ok (.Ok (),updated) at late_run
  rw [ready] at late_call
  rw [late_call] at late_run
  change ok (.Ok (),NBN_LateTail.value c.lane_transition NBN_LateResult.header) = ok (.Ok (),updated) at late_run
  have same : NBN_LateTail.value c.lane_transition NBN_LateResult.header = updated :=
    congrArg Prod.snd (Result.ok.inj late_run)
  have pay_call := AspisS6OuterNativeOps.withdrawal_return p
  rw [pay_run] at pay_call
  change ok (.Ok pay) = pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p at pay_call
  have bytes_equal : encoded = NBN_EncoderBytes.bytes (.Withdrawal c p) pay := by
    apply Subtype.ext
    rw [layout,← same]
    rfl
  refine ⟨pay,pay_call.symm,?_⟩
  unfold AspisS6OuterNativeInstalled.encode
  change resultMap _ (AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_statement_v1 nativeOps
    (.Withdrawal (fromPoolV1PairForestTerminalCommonV1 c) (fromPoolV1WithdrawalPublicV1 p))) = _
  rw [run,bytes_equal]
  rfl

#print axioms private_contents
#print axioms withdrawal_contents
end NBN_EncoderContents
