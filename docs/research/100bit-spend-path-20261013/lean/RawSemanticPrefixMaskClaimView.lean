import R1SemanticPayloadView
import RawSemanticPrefixMaskClaim

set_option autoImplicit false
namespace AspisR1.RawSemanticPrefixMaskClaimView
open AspisR1.SemanticRecordCodec

theorem claimAt14_eq_claimPayloadAt14 (values : AspisR1.SemanticPrefixCodec.Full) :
    AspisR1.RawSemanticPrefixMaskClaim.claimAt14 values =
      AspisR1.SemanticPayloadView.claimPayloadAt14 values := by
  have hcodec := AspisR1.RawSemanticPrefixMaskClaim.claimAt14_payload values
  have hview := AspisR1.SemanticPayloadView.claimAt14_payload values
  have heq : Payload.maskSum (AspisR1.RawSemanticPrefixMaskClaim.claimAt14 values) =
      Payload.maskSum (AspisR1.SemanticPayloadView.claimPayloadAt14 values) :=
    hcodec.symm.trans hview
  injection heq

theorem claimAt14_val_eq_view (values : AspisR1.SemanticPrefixCodec.Full) :
    (AspisR1.RawSemanticPrefixMaskClaim.claimAt14 values).val =
      AspisR1.SemanticPayloadView.claimAt14 values := by
  rw [claimAt14_eq_claimPayloadAt14]
  rfl

#print axioms claimAt14_eq_claimPayloadAt14
#print axioms claimAt14_val_eq_view
end AspisR1.RawSemanticPrefixMaskClaimView
