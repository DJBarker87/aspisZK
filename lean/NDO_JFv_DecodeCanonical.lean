import NDO_JFv_SemanticDecode
import RPz7_F3P_DecodeCells
import RPu_JFv_RawExtractedSemanticCallOpsV20
import AspisR1DecodeKFullSuccessCanonicality
set_option autoImplicit false
namespace AspisR1.JFv_DecodeCanonical
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open RawExtractedSemanticCallOpsV20
open AspisR1.ExtractedMaskQM31Exact

theorem source {N : Usize} (r : r1_wire.ValidatedRecord) (offset : Usize)
    (out : Array AspisS1ExtractedRoundChildren.MainQM N)
    (call : AspisS1ExtractedRoundChildren.decodeMain N r offset=ok (.Ok out)) :
    ∀ j : Fin N.val,CurrentCanonicalQM
      (genQToProbe (AspisS1ExtractedRoundChildren.mainToGen
        (out.val[j.val]'(by simpa only [out.property] using j.isLt)))) := by
  obtain ⟨decoded,run,same⟩ := F3P_DecodeCells.source r offset out call
  have canonical := AspisR1DecodeKFullSuccessCanonicality.decode_k_success_canonical N
    (AspisS1ExtractedRoundChildren.recordToDecoder r) offset decoded run
  subst out
  intro j
  have h := canonical j
  simpa only [AspisS1ExtractedRoundChildren.decoderArrayToMain,List.getElem_map,
    AspisS1ExtractedRoundChildren.decoderQMToMain,AspisS1ExtractedRoundChildren.mainToGen,
    genQToProbe,genCToProbe,CurrentCanonicalQM,
    AspisR1.ExtractedMaskTowerAdd.CanonicalQM,AspisR1.ExtractedMaskTowerAdd.CanonicalCM,
    AspisR1.ExtractedMaskTowerAdd.P,AspisR1.ExtractedMaskM31AddSub.P,
    AspisR1DecodeKCanonicalArrayInvariant.Canonical,
    AspisR1DecodeKFullV10.aspis_core.field.P, show (2147483647#u32).val=2147483647 from rfl, and_assoc] using h

#print axioms source
end AspisR1.JFv_DecodeCanonical
