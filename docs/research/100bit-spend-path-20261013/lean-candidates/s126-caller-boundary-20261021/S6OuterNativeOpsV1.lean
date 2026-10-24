import S6OuterCarrierBridgeV1
import S6FullForestEncoderNamedNativeV1
import S6NativeForestValidatorTotalV1
import S6NativePaymentEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6OuterNativeOps
open AspisS6OuterCarrierBridge

def rustMapError {T E F : Type} (f : E → F) : core.result.Result T E → core.result.Result T F
  | .Ok value => .Ok value
  | .Err error => .Err (f error)

def resultMap {T U : Type} (f : T → U) : Result T → Result U
  | .ok value => .ok (f value)
  | .fail error => .fail error
  | .div => .div

def nativeOps : AspisS6FullForestEncoderNamed.Ops where
  digest := AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical
  validate := fun value => resultMap (rustMapError fromPoolV1PairForestTerminalFormatErrorV1)
    (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      (toPoolV1PairForestTerminalStatementV1 value))
  withdrawal := fun value => resultMap (rustMapError fromPoolV1PaymentStatementFormatError)
    (AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
      (toPoolV1WithdrawalPublicV1 value))
  transfer := fun value => resultMap (rustMapError fromPoolV1PaymentStatementFormatError)
    (AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
      (toPoolV1PrivateTransferPublicV1 value))
  late := fun value output => resultMap
    (fun result => (rustMapError fromPoolV1PairLatePublicStatementErrorV1 result.1,result.2))
    (AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
      (toPoolV1PairLatePublicStatementV1 value) output)

theorem validate_call (value : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
    nativeOps.validate (fromPoolV1PairForestTerminalStatementV1 value) =
      resultMap (rustMapError fromPoolV1PairForestTerminalFormatErrorV1) (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 value) := by
  simp only [nativeOps,to_fromPoolV1PairForestTerminalStatementV1]

#print axioms validate_call

theorem withdrawal_call (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    nativeOps.withdrawal (fromPoolV1WithdrawalPublicV1 value) =
      resultMap (rustMapError fromPoolV1PaymentStatementFormatError) (AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 value) := by
  simp only [nativeOps,to_fromPoolV1WithdrawalPublicV1]

#print axioms withdrawal_call

theorem transfer_call (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    nativeOps.transfer (fromPoolV1PrivateTransferPublicV1 value) =
      resultMap (rustMapError fromPoolV1PaymentStatementFormatError) (AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 value) := by
  simp only [nativeOps,to_fromPoolV1PrivateTransferPublicV1]

#print axioms transfer_call

theorem late_call (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) (output : Slice U8) :
    nativeOps.late (fromPoolV1PairLatePublicStatementV1 value) output =
      resultMap (fun result => (rustMapError fromPoolV1PairLatePublicStatementErrorV1 result.1,result.2)) (AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 value output) := by
  simp only [nativeOps,to_fromPoolV1PairLatePublicStatementV1]

#print axioms late_call

theorem kind_read (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind) :
    (read_discriminant (toPoolV1TransitionKind value) : U8)=(read_discriminant value : U8) := by
  cases value <;> rfl

#print axioms nativeOps
#print axioms kind_read
end AspisS6OuterNativeOps
