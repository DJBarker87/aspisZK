import NDO_JFs_PaymentDecode
import NDO_JFs_LateDecode
import RPz7_S6NativePaymentAcceptedInverseV1
import RPz7_S6NativeLateEncodeSuccessV1
set_option autoImplicit false
namespace AspisR1.JFs_PublicEncoders
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem payment : ∃ encoded : Array U8 216#usize, encoded.val=JFu_PublicRange.payment.val ∧
    pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 JFs_PaymentValue.value=
      ok (.Ok encoded) :=
  AspisS6NativePaymentContents.transfer_accepted_inverse _ _ JFs_PaymentDecode.source

theorem late : ∃ updated : Slice U8,
    pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 JFs_LateChildren.value
      (Array.to_slice (Array.repeat 1520#usize 0#u8))=ok (.Ok (),updated) ∧ updated.length=1520 := by
  apply AspisS6NativeLateEncodeAccepted.encode_from_decode _ _ JFs_LateDecode.source
  simp only [Array.to_slice,Array.repeat,Slice.length,List.length_replicate]
  rfl

#print axioms payment
#print axioms late
end AspisR1.JFs_PublicEncoders
