import NDO_JHi_PaymentValidation
set_option autoImplicit false
namespace AspisR1.JHi_CommonEncoder
open Aeneas Aeneas.Std Result

def raw (c : AspisR1TerminalDecoder.pool_v1.payment_relation.CommonPublicV1) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.CommonPublicV1 :=
  ⟨c.pool,c.deployment_domain,c.anchor_sequence,c.anchor_root,c.nullifier,c.asset_id⟩

/-- Source operation association; generic arrays prevent concrete-buffer reduction. -/
theorem source (out : Array U8 216#usize) (magic : Array U8 4#usize)
    (c : AspisR1TerminalDecoder.pool_v1.payment_relation.CommonPublicV1) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common out magic
      .PrivateTransfer (raw c)=
    AspisR1TerminalDecoder.pool_v1.payment_relation.encode_common out magic .PrivateTransfer c := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common
    AspisR1TerminalDecoder.pool_v1.payment_relation.encode_common
  simp only [JHi_DigestAssociation.encode]
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
    AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.AMOUNT_OR_RESERVED_OFFSET
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.ANCHOR_ROOT_OFFSET
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.ANCHOR_SEQUENCE_OFFSET
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.ASSET_ID_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.ASSET_ID_OFFSET
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.DEPLOYMENT_DOMAIN_OFFSET
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.NULLIFIER_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.NULLIFIER_OFFSET
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.POOL_OFFSET
    AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_OFFSET
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION
    AspisR1TerminalDecoder.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_VERSION
  rfl
#print axioms source
end AspisR1.JHi_CommonEncoder
