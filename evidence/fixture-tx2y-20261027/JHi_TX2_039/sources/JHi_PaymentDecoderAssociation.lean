import JHi_PaymentBody
import JHi_CommonEncoder
set_option autoImplicit false
namespace AspisR1.JHi_PaymentDecoderAssociation
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct
open JHi_PaymentBody
theorem source :
    AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
      JFs_PaymentValue.value =
    (body >>= fun x=>ok (core.result.Result.Ok x : core.result.Result _
      AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) := by
  unfold AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
  rw [JFs_PaymentValue.validated]
  simp only [bind_tc_ok,AspisR1TerminalDecoder.core.result.Result.Insts.CoreOpsTry.branch]
  simp only [body,aspis_statement.pool_v1.payment_relation.transfer_common,
    AspisR1TerminalDecoder.pool_v1.payment_relation.transfer_common,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  have common : (⟨JHg_RawPrefix.payment.pool,JHg_RawPrefix.payment.deployment_domain,
      JHg_RawPrefix.payment.anchor_sequence,JHg_RawPrefix.payment.anchor_root,
      JHg_RawPrefix.payment.nullifier,JHg_RawPrefix.payment.asset_id⟩ :
      aspis_statement.pool_v1.payment_relation.CommonPublicV1)=
      JHi_CommonEncoder.raw JFs_PaymentValue.common := rfl
  rw [common,JHi_CommonEncoder.source]
  simp only [JHi_DigestAssociation.encode]
  unfold aspis_statement.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
    AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
    aspis_statement.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET
    aspis_statement.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
  rfl
#print axioms source
end AspisR1.JHi_PaymentDecoderAssociation
