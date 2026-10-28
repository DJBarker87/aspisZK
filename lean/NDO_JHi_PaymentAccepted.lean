import NDO_JHi_PaymentRawAction
import NDO_JHi_PaymentDecoderAction
import NDO_JFs_PublicEncoders
set_option autoImplicit false
namespace AspisR1.JHi_PaymentAccepted
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

theorem source : ∃ encoded : Array U8 216#usize,
    aspis_statement.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1
      JHg_RawPrefix.payment=ok (.Ok encoded) := by
  obtain ⟨encoded,_,run⟩:=JFs_PublicEncoders.payment
  have valid : aspis_statement.pool_v1.payment_relation.validate_pool_v1_private_transfer_public_v1
      (JHi_PaymentAction.raw JFs_PaymentValue.value)=ok (.Ok ()) := JHi_PaymentValidation.source
  have decoder:=JHi_PaymentDecoderAction.source JFs_PaymentValue.value JFs_PaymentValue.validated
  rw [decoder] at run
  have raw:=JHi_PaymentRawAction.source JFs_PaymentValue.value valid
  have success : (JHi_PaymentAction.body JFs_PaymentValue.value >>= fun x=>ok
      (core.result.Result.Ok x : core.result.Result _
        aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError))=ok (.Ok encoded) :=
    JHi_RetypeSuccess.source _ _ run
  have same : JHi_PaymentAction.raw JFs_PaymentValue.value=JHg_RawPrefix.payment := rfl
  exact ⟨encoded, same ▸ raw.trans success⟩
#print axioms source
end AspisR1.JHi_PaymentAccepted
