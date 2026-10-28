import NBP_PaymentModel
set_option autoImplicit false
noncomputable section
namespace NBP_TransferEncode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBP_PaymentModel

theorem result (p : T) : pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p = ok (transfer_encoded p) := by
  simp only [pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1,NBG_PaymentValidators.transfer_result,
    transfer_encoded,bind_tc_ok]
  cases h : NBG_PaymentValidators.transfer p with
  | Err e =>
    simp [h,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp only [h,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    have projected : pool_v1.payment_relation.transfer_common p = ok (NBG_PaymentValidators.tc p) := NBG_Atomic.transfer_projection p
    rw [projected]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    rw [NBP_CommonBytes.result]
    simp only [bind_tc_ok,NBP_DigestEncode.result,lift,
      pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET,
      pool_v1.payment_relation.SECOND_OUTPUT_OFFSET,
      pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET]
    unfold transfer_bytes
    generalize h0 : NBP_CommonBytes.encoded (Array.repeat 216#usize 0#u8) pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC .PrivateTransfer (NBG_PaymentValidators.tc p) = o0
    rw [NBP_ArrayIndex.index_mut o0 152#usize 184#usize (by decide) (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NBP_ArrayIndex.slice o0 152#usize 184#usize) (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment).to_slice; _) = _
    rw [NBP_ArrayIndex.copy_range o0 152#usize 184#usize (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    generalize h1 : o0.setSlice! 152 (AspisR1.S2K.DigestBytes.bytes p.recipient_commitment).val = o1
    rw [NBP_ArrayIndex.suffix_index o1 184#usize (by decide)]
    change (do let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 (NBP_ArrayIndex.slice o1 184#usize 216#usize) (AspisR1.S2K.DigestBytes.bytes p.change_commitment).to_slice; _) = _
    rw [NBP_ArrayIndex.copy_range o1 184#usize 216#usize (AspisR1.S2K.DigestBytes.bytes p.change_commitment) (by decide) (by decide) (by decide)]
    simp only [bind_tc_ok,Array.to_slice,UScalar.ofNatCore_val_eq]
    try rfl
#print axioms result
end NBP_TransferEncode
