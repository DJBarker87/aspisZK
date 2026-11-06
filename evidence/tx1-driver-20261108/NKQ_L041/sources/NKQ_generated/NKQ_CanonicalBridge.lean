import NKQ_MaskCuts
import JFv_RoundArithmetic
set_option autoImplicit false
namespace AspisR1.NKQ_CanonicalBridge
open Aeneas Aeneas.Std AspisR1PublicPreparation

theorem canonical (q : aspis_core.field.QM31) :
 JFv_RoundArithmetic.Canonical q ↔ NKQ_MaskCuts.Canon q := by rfl

theorem selected (q : aspis_core.field.QM31) :
 RawExtractedSemanticCallOpsV20.CurrentCanonicalQM
  (RawExtractedSemanticCallOpsV20.genQToProbe (AspisS1ExtractedRoundChildren.mainToGen q)) ↔
 NKQ_MaskCuts.Canon q := by rfl
#print axioms canonical
#print axioms selected
end AspisR1.NKQ_CanonicalBridge
