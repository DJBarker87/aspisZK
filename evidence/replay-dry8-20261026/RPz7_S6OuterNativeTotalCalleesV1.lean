import RPz7_S6OuterNativeInstalledV1
import RPz7_S6NativeLateEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6OuterNativeTotalCallees
open AspisS6OuterNativeOps AspisS6OuterCarrierBridge

@[step] theorem validate_spec (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
    nativeOps.validate value ⦃ _ => True ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativeForestTotal.validate_total (toPoolV1PairForestTerminalStatementV1 value)
  unfold nativeOps
  simp only [run,resultMap,WP.spec_ok]

#print axioms validate_spec

@[step] theorem withdrawal_spec (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    nativeOps.withdrawal value ⦃ _ => True ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativePaymentEncodeTotal.withdrawal_write_total (toPoolV1WithdrawalPublicV1 value)
  unfold nativeOps
  simp only [run,resultMap,WP.spec_ok]

#print axioms withdrawal_spec

@[step] theorem transfer_spec (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    nativeOps.transfer value ⦃ _ => True ⦄ := by
  obtain ⟨result,run⟩ := AspisS6NativePaymentEncodeTotal.transfer_write_total (toPoolV1PrivateTransferPublicV1 value)
  unfold nativeOps
  simp only [run,resultMap,WP.spec_ok]

#print axioms transfer_spec

@[step] theorem late_spec
    (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (output : Slice U8) : nativeOps.late value output ⦃ result => result.2.length=output.length ⦄ := by
  obtain ⟨⟨status,updated⟩,run,frame⟩ := AspisS6NativeLateEncodeTotal.encode_total
    (toPoolV1PairLatePublicStatementV1 value) output
  unfold nativeOps
  simp only [run,resultMap,WP.spec_ok]
  exact frame

#print axioms late_spec
end AspisS6OuterNativeTotalCallees
