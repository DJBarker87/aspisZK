import NKQ_MaskCuts
set_option autoImplicit false
namespace AspisR1.NKQ_CanonicalBridge
open Aeneas Aeneas.Std AspisR1PublicPreparation

theorem canonical (q : aspis_core.field.QM31) :
 JFv_RoundArithmetic.Canonical q ↔ NKQ_MaskCuts.Canon q := by
 simp only [JFv_RoundArithmetic.Canonical,
  AspisS1ExtractedRoundChildren.mainToGen,
  RawExtractedSemanticCallOpsV20.genQToProbe,RawExtractedSemanticCallOpsV20.genCToProbe,
  AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM,
  AspisR1.ExtractedMaskTowerAdd.CanonicalQM,AspisR1.ExtractedMaskTowerAdd.CanonicalCM,
  AspisR1.ExtractedMaskTowerAdd.P,AspisR1.ExtractedMaskM31AddSub.P,
  NKQ_MaskCuts.Canon,and_assoc]

#print axioms canonical
end AspisR1.NKQ_CanonicalBridge
