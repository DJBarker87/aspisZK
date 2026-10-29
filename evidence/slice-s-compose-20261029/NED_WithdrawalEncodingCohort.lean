import NED_CommonEncodeCohort
import NBP_WithdrawalEncode
set_option autoImplicit false
noncomputable section
namespace NED_WithdrawalEncodingCohort
open Aeneas Aeneas.Std Result NED_PaymentCohorts NED_CommonValidation
open AspisR1AdapterReconstruct

theorem result (p : W) :
    aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 (toRawWithdrawal p) =
    ok (mapPayment (NBP_PaymentModel.withdrawal_encoded p)) := by
  simp only [aspis_statement.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1,
    NED_PaymentValidation.withdrawal_result,bind_tc_ok]
  unfold NBP_PaymentModel.withdrawal_encoded
  cases h : NBG_PaymentValidators.withdrawal p with
  | Err e =>
    simp [h,mapPayment,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp only [h,mapPayment,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    rw [NED_PaymentCohorts.withdrawal_common]
    simp only [bind_tc_ok]
    have encoded := NED_CommonEncodeCohort.result (Array.repeat 216#usize 0#u8)
      aspis_statement.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC
      .Withdrawal (NBG_PaymentValidators.wc p)
    simp only [NED_CommonEncodeCohort.toRawKind] at encoded
    rw [encoded]
    simp only [bind_tc_ok,NED_DigestCohorts.digest_encode,NBP_DigestEncode.result,lift,
      aspis_statement.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
      aspis_statement.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
      aspis_statement.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET]
    simp only [toRawWithdrawal,AspisR1.JHf_Carrier.toPoolV1WithdrawalPublicV1,
      AspisS6CurrentAdapterCarrier.fromPoolV1WithdrawalPublicV1]
    unfold NBP_PaymentModel.withdrawal_bytes
    simp only [aspis_statement.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC,
      AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC]
    generalize common : NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8)
      (Array.make 4#usize [65#u8,83#u8,87#u8,80#u8])
      AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal
      (NBG_PaymentValidators.wc p) = out
    rw [NBP_ArrayIndex.index_mut out 148#usize 152#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NBP_ArrayIndex.slice out 148#usize 152#usize) (core.num.U32.to_le_bytes p.amount).to_slice; _) = _
    rw [NBP_ArrayIndex.copy_range out 148#usize 152#usize (core.num.U32.to_le_bytes p.amount) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize amount : out.setSlice! 148 (core.num.U32.to_le_bytes p.amount).val = out1
    rw [NBP_ArrayIndex.index_mut out1 152#usize 184#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NBP_ArrayIndex.slice out1 152#usize 184#usize) p.destination_token_account.to_slice; _) = _
    rw [NBP_ArrayIndex.copy_range out1 152#usize 184#usize p.destination_token_account (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize destination : out1.setSlice! 152 p.destination_token_account.val = out2
    rw [NBP_ArrayIndex.suffix_index out2 184#usize (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NBP_ArrayIndex.slice out2 184#usize 216#usize) (AspisR1.S2K.DigestBytes.bytes p.change_commitment).to_slice; _) = _
    rw [NBP_ArrayIndex.copy_range out2 184#usize 216#usize (AspisR1.S2K.DigestBytes.bytes p.change_commitment) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    try rfl

#print axioms result
end NED_WithdrawalEncodingCohort
