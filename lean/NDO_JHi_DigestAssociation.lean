import NDO_JHg_RawPrefix
import NDO_JFs_PaymentCanon
set_option autoImplicit false
namespace AspisR1.JHi_DigestAssociation
open Aeneas Aeneas.Std Result

theorem canonical (digest : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.digest_is_canonical digest =
    AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical digest := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.digest_is_canonical
    AspisR1TerminalDecoder.pool_v1.payment_relation.digest_is_canonical
    AspisR1AdapterReconstruct.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl
#print axioms canonical

theorem encode (digest : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.atomic_statement.encode_digest_canonical digest =
    AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical digest := by rfl
#print axioms encode
end AspisR1.JHi_DigestAssociation
