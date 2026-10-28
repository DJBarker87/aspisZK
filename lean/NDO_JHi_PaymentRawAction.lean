import NDO_JHi_PaymentAction
set_option autoImplicit false
namespace AspisR1.JHi_PaymentRawAction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct JHi_PaymentAction

theorem source (p : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (validated : aspis_statement.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1 (raw p)=ok (.Ok ())) :
    aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 (raw p)=
    (body p >>= fun x=>ok (core.result.Result.Ok x : core.result.Result _
      aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError)) := by
  unfold aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
  rw [validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [body,aspis_statement.pool_v1.payment_relation.transfer_common,
    AspisR1TerminalDecoder.pool_v1.payment_relation.transfer_common,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry]
  change _ = _
  have common : (⟨(raw p).pool,(raw p).deployment_domain,(raw p).anchor_sequence,
      (raw p).anchor_root,(raw p).nullifier,(raw p).asset_id⟩ :
      aspis_statement.pool_v1.payment_relation.CommonPublicV1) =
      JHi_CommonEncoder.raw
        (⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id⟩ :
          AspisR1TerminalDecoder.pool_v1.payment_relation.CommonPublicV1) := rfl
  rw [common,JHi_CommonEncoder.source]
  simp only [JHi_DigestAssociation.encode,raw]
  unfold aspis_statement.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
    AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC
  unfold aspis_statement.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.FIRST_OUTPUT_OR_DESTINATION_OFFSET
  unfold aspis_statement.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.SECOND_OUTPUT_OFFSET
  congr 1
#print axioms source
end AspisR1.JHi_PaymentRawAction
