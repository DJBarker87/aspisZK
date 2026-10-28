import NBP_PaymentModel
set_option autoImplicit false
noncomputable section
namespace NBP_WithdrawalEncode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBP_PaymentModel

theorem result (p : W) : pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p = ok (withdrawal_encoded p) := by
  simp only [pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1,NBG_PaymentValidators.withdrawal_result,
    withdrawal_encoded,bind_tc_ok]
  cases h : NBG_PaymentValidators.withdrawal p with
  | Err e =>
    simp [h,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp only [h,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    have projected : pool_v1.payment_relation.withdrawal_common p = ok (NBG_PaymentValidators.wc p) := NBG_Atomic.withdrawal_projection p
    rw [projected]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    rw [NBP_CommonBytes.result]
    simp only [bind_tc_ok,NBP_DigestEncode.result,lift,
      pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
      pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
      pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET]
    unfold withdrawal_bytes
    generalize h0 : NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8) pool_v1.payment_relation.POOL_V1_WITHDRAWAL_STATEMENT_MAGIC .Withdrawal (NBG_PaymentValidators.wc p) = o0
    rw [NBP_ArrayIndex.index_mut o0 148#usize 152#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NBP_ArrayIndex.slice o0 148#usize 152#usize) (core.num.U32.to_le_bytes p.amount).to_slice; _) = _
    rw [NBP_ArrayIndex.copy_range o0 148#usize 152#usize (core.num.U32.to_le_bytes p.amount) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize h1 : o0.setSlice! 148 (core.num.U32.to_le_bytes p.amount).val = o1
    rw [NBP_ArrayIndex.index_mut o1 152#usize 184#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NBP_ArrayIndex.slice o1 152#usize 184#usize) p.destination_token_account.to_slice; _) = _
    rw [NBP_ArrayIndex.copy_range o1 152#usize 184#usize p.destination_token_account (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize h2 : o1.setSlice! 152 p.destination_token_account.val = o2
    rw [NBP_ArrayIndex.suffix_index o2 184#usize (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NBP_ArrayIndex.slice o2 184#usize 216#usize) (AspisR1.S2K.DigestBytes.bytes p.change_commitment).to_slice; _) = _
    rw [NBP_ArrayIndex.copy_range o2 184#usize 216#usize (AspisR1.S2K.DigestBytes.bytes p.change_commitment) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    try rfl
#print axioms result
end NBP_WithdrawalEncode
