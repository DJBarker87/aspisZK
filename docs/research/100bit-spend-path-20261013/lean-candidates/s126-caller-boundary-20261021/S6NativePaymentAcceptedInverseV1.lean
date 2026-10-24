import S6NativePaymentWriterContentsV1
import S6ZeroWordBytesV1
import S6NativePaymentEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativePaymentContents
open AspisR1TerminalDecoder
open pool_v1.payment_relation

/-- The frozen fee is exactly zero; only four zero bytes are reduced here. -/
theorem fee_bytes_zero :
    (core.num.U32.to_le_bytes POOL_V1_CANONICAL_FEE).val=List.replicate 4 0#u8 := by
  simpa only [POOL_V1_CANONICAL_FEE] using AspisS6ZeroWord.u32_zero

/-- Complete 216-byte accepted transfer inverse. Every binding, validation and
child return is derived from this decoder execution; no independent premises. -/
theorem transfer_accepted_inverse (bytes : Slice U8) (public1 : PoolV1PrivateTransferPublicV1)
    (accepted : decode_pool_v1_private_transfer_public_v1 bytes=ok (core.result.Result.Ok public1)) :
    ∃ encoded : Array U8 216#usize, encoded.val=bytes.val ∧
      encode_pool_v1_private_transfer_public_v1 public1=ok (core.result.Result.Ok encoded) := by
  have frames := AspisS6NativePaymentDecode.transfer_frames bytes
  rw [accepted,WP.spec_ok] at frames
  rcases frames public1 rfl with
    ⟨raw,hraw,header,⟨common,binding,fields⟩,fee,
      ⟨recipient,hr,hrbytes⟩,⟨change,hc,hcbytes⟩,valid⟩
  have hp := accepted_common_prefix raw _ _ common header fields
  have hr' := (encoded_digest_chunks public1.recipient_commitment recipient hr).trans hrbytes
  have hc' := (encoded_digest_chunks public1.change_commitment change hc).trans hcbytes
  have hf : List.replicate 4 0#u8=List.slice 148 152 raw.val :=
    (fee.trans fee_bytes_zero).symm
  have hb : transfer_bytes common public1=raw.val := by
    unfold transfer_bytes
    rw [hp,hf,hr',hc',
      AspisS6SliceFrame.take_append_slice raw.val 148 152 (by decide),
      AspisS6SliceFrame.take_append_slice raw.val 152 184 (by decide),
      List.take_append_drop]
  obtain ⟨result,hresult⟩ := AspisS6NativePaymentEncodeTotal.transfer_write_total public1
  have written := transfer_write public1 common binding valid
  rw [hresult,WP.spec_ok] at written
  rcases written with ⟨output,ho,hoval⟩
  have heq : output=raw := Subtype.ext (hoval.trans hb)
  refine ⟨raw,hraw,?_⟩
  simpa only [ho,heq] using hresult

/-- Complete 216-byte accepted withdrawal inverse, on arbitrary input slices. -/
theorem withdrawal_accepted_inverse (bytes : Slice U8) (public1 : PoolV1WithdrawalPublicV1)
    (accepted : decode_pool_v1_withdrawal_public_v1 bytes=ok (core.result.Result.Ok public1)) :
    ∃ encoded : Array U8 216#usize, encoded.val=bytes.val ∧
      encode_pool_v1_withdrawal_public_v1 public1=ok (core.result.Result.Ok encoded) := by
  have frames := AspisS6NativePaymentDecode.withdrawal_frames bytes
  rw [accepted,WP.spec_ok] at frames
  rcases frames public1 rfl with
    ⟨raw,hraw,header,⟨common,binding,fields⟩,amount,destination,
      ⟨change,hc,hcbytes⟩,valid⟩
  have hp := accepted_common_prefix raw _ _ common header fields
  have hc' := (encoded_digest_chunks public1.change_commitment change hc).trans hcbytes
  have hb : withdrawal_bytes common public1=raw.val := by
    unfold withdrawal_bytes
    rw [hp,amount,destination,hc',
      AspisS6SliceFrame.take_append_slice raw.val 148 152 (by decide),
      AspisS6SliceFrame.take_append_slice raw.val 152 184 (by decide),
      List.take_append_drop]
  obtain ⟨result,hresult⟩ := AspisS6NativePaymentEncodeTotal.withdrawal_write_total public1
  have written := withdrawal_write public1 common binding valid
  rw [hresult,WP.spec_ok] at written
  rcases written with ⟨output,ho,hoval⟩
  have heq : output=raw := Subtype.ext (hoval.trans hb)
  refine ⟨raw,hraw,?_⟩
  simpa only [ho,heq] using hresult

#print axioms fee_bytes_zero
#print axioms transfer_accepted_inverse
#print axioms withdrawal_accepted_inverse
end AspisS6NativePaymentContents
