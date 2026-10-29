import NED_PaymentResultTransport
set_option autoImplicit false
noncomputable section
namespace NED_PaymentValidation
open Aeneas Aeneas.Std Result NED_PaymentCohorts NED_CommonValidation
open AspisR1AdapterReconstruct

theorem transfer_result (p : T) :
    aspis_statement.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 (toRawTransfer p) =
    ok (mapPayment (NBG_PaymentValidators.transfer p)) := by
  unfold aspis_statement.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1
  rw [NED_PaymentCohorts.transfer_common,bind_tc_ok,NED_CommonValidation.common_result,bind_tc_ok]
  cases h : NBG_PaymentChecks.common (NBG_PaymentValidators.tc p) with
  | Err e => simp [NBG_PaymentValidators.transfer,h,mapPayment,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp [NBG_PaymentValidators.transfer,h,mapPayment,NED_PaymentResultTransport.map_ite,canonical_result,
      toRawTransfer,AspisR1.JHf_Carrier.toPoolV1PrivateTransferPublicV1,
      AspisS6CurrentAdapterCarrier.fromPoolV1PrivateTransferPublicV1,
      core.result.Result.Insts.CoreOpsTry.branch,NED_ErrorCarriers.toRawPoolV1PaymentStatementFormatError]
    repeat' split
    all_goals simp_all

theorem value_limit : aspis_statement.spend.VALUE_LIMIT = ok 1073741824#u32 := by
  unfold aspis_statement.spend.VALUE_LIMIT
  rfl

theorem withdrawal_result (p : W) :
    aspis_statement.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1 (toRawWithdrawal p) =
    ok (mapPayment (NBG_PaymentValidators.withdrawal p)) := by
  unfold aspis_statement.pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1
  rw [NED_PaymentCohorts.withdrawal_common,bind_tc_ok,NED_CommonValidation.common_result,bind_tc_ok]
  cases h : NBG_PaymentChecks.common (NBG_PaymentValidators.wc p) with
  | Err e => simp [NBG_PaymentValidators.withdrawal,h,mapPayment,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    by_cases large : 1073741824 ≤ p.amount.val <;>
      simp [NBG_PaymentValidators.withdrawal,h,large,mapPayment,NED_PaymentResultTransport.map_ite,canonical_result,
      toRawWithdrawal,AspisR1.JHf_Carrier.toPoolV1WithdrawalPublicV1,
      AspisS6CurrentAdapterCarrier.fromPoolV1WithdrawalPublicV1,
      NBG_PaymentChecks.zero_result,value_limit,
      core.result.Result.Insts.CoreOpsTry.branch,NED_ErrorCarriers.toRawPoolV1PaymentStatementFormatError]
    all_goals repeat' split
    all_goals simp_all +arith <;> scalar_tac

#print axioms transfer_result
#print axioms value_limit
#print axioms withdrawal_result
end NED_PaymentValidation
