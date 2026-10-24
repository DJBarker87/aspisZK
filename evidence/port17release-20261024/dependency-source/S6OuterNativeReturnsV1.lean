import S6OuterNativeOpsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6OuterNativeOps
open AspisS6OuterCarrierBridge

theorem result_error_cancel {T E F : Type} (f : E → F) (g : F → E)
    (inverse : ∀ error, g (f error)=error) (result : Result (core.result.Result T E)) :
    resultMap (rustMapError g) (resultMap (rustMapError f) result)=result := by
  cases result with
  | fail error => rfl
  | div => rfl
  | ok value => cases value <;> simp only [resultMap,rustMapError,inverse]

theorem result_pair_cancel {T E F U : Type} (f : E → F) (g : F → E)
    (inverse : ∀ error, g (f error)=error) (result : Result (core.result.Result T E × U)) :
    resultMap (fun pair => (rustMapError g pair.1,pair.2))
      (resultMap (fun pair => (rustMapError f pair.1,pair.2)) result)=result := by
  cases result with
  | fail error => rfl
  | div => rfl
  | ok pair => rcases pair with ⟨value,output⟩; cases value <;> simp only [resultMap,rustMapError,inverse]

theorem digest_call (digest : Array U32 8#usize) :
    nativeOps.digest digest=AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical digest := rfl

theorem validate_return (value : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
    resultMap (rustMapError toPoolV1PairForestTerminalFormatErrorV1) (nativeOps.validate (fromPoolV1PairForestTerminalStatementV1 value)) =
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 value := by
  rw [validate_call]
  exact result_error_cancel fromPoolV1PairForestTerminalFormatErrorV1 toPoolV1PairForestTerminalFormatErrorV1 to_fromPoolV1PairForestTerminalFormatErrorV1 _

#print axioms validate_return

theorem withdrawal_return (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    resultMap (rustMapError toPoolV1PaymentStatementFormatError) (nativeOps.withdrawal (fromPoolV1WithdrawalPublicV1 value)) =
      AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 value := by
  rw [withdrawal_call]
  exact result_error_cancel fromPoolV1PaymentStatementFormatError toPoolV1PaymentStatementFormatError to_fromPoolV1PaymentStatementFormatError _

#print axioms withdrawal_return

theorem transfer_return (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    resultMap (rustMapError toPoolV1PaymentStatementFormatError) (nativeOps.transfer (fromPoolV1PrivateTransferPublicV1 value)) =
      AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 value := by
  rw [transfer_call]
  exact result_error_cancel fromPoolV1PaymentStatementFormatError toPoolV1PaymentStatementFormatError to_fromPoolV1PaymentStatementFormatError _

#print axioms transfer_return

theorem late_return (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) (output : Slice U8) :
    resultMap (fun pair => (rustMapError toPoolV1PairLatePublicStatementErrorV1 pair.1,pair.2)) (nativeOps.late (fromPoolV1PairLatePublicStatementV1 value) output) =
      AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 value output := by
  rw [late_call]
  exact result_pair_cancel fromPoolV1PairLatePublicStatementErrorV1 toPoolV1PairLatePublicStatementErrorV1 to_fromPoolV1PairLatePublicStatementErrorV1 _

#print axioms late_return

#print axioms result_error_cancel
#print axioms result_pair_cancel
#print axioms digest_call
end AspisS6OuterNativeOps
