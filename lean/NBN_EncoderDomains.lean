import NBN_LateInvariant
import S6OuterEncoderContentsV1
set_option autoImplicit false
noncomputable section
namespace NBN_EncoderDomains
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult
open AspisS6OuterNativeOps AspisS6OuterCarrierBridge
open pool_v1.pair_forest_terminal

theorem late (s : Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    AspisS6OuterEncodeSuccess.late_ready
      (fromPoolV1PairLatePublicStatementV1 (common s).lane_transition) := by
  intro output size
  obtain ⟨run,len⟩ := NBN_LateInvariant.statement_ready s valid output size
  refine ⟨NBN_LateTail.value (common s).lane_transition NBN_LateResult.header,?_,len⟩
  rw [late_call,run]
  rfl

theorem transfer (c : PoolV1PairForestTerminalCommonV1)
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 (.PrivateTransfer c p) = ok (.Ok ())) :
    ∃ bytes, nativeOps.transfer (fromPoolV1PrivateTransferPublicV1 p) = ok (.Ok bytes) := by
  obtain ⟨bytes,run,_⟩ := NBN_StatementDomains.payment_reached (.PrivateTransfer c p) valid
  change pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p = ok (.Ok bytes) at run
  refine ⟨bytes,?_⟩
  rw [transfer_call,run]
  rfl

theorem withdrawal (c : PoolV1PairForestTerminalCommonV1)
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 (.Withdrawal c p) = ok (.Ok ())) :
    ∃ bytes, nativeOps.withdrawal (fromPoolV1WithdrawalPublicV1 p) = ok (.Ok bytes) := by
  obtain ⟨bytes,run,_⟩ := NBN_StatementDomains.payment_reached (.Withdrawal c p) valid
  change pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p = ok (.Ok bytes) at run
  refine ⟨bytes,?_⟩
  rw [withdrawal_call,run]
  rfl

theorem validator (s : Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    nativeOps.validate (fromPoolV1PairForestTerminalStatementV1 s) = ok (.Ok ()) := by
  rw [validate_call,valid]
  rfl

#print axioms late
#print axioms transfer
#print axioms withdrawal
#print axioms validator
end NBN_EncoderDomains
