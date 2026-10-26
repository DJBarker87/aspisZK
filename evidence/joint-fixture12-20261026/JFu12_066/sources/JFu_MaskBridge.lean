import FIp_MaskValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_MaskBridge
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic

theorem source (c1 : Array MQ 16#usize) (maskOnly : Array MQ 10#usize) (g : MQ) (point : Array MQ 10#usize)
    (c1_canonical : ∀ i : Fin 16,ExtractedMaskCallerModel.CanonicalQM
      (ExtractedMaskCoefficientStep.c1Cell (mapArray c1) i))
    (maskOnly_canonical : ∀ i : Fin 10,ExtractedMaskCallerModel.CanonicalQM
      (ExtractedMaskCoefficientStep.maskCell (mapArray maskOnly) i))
    (point_canonical : ∀ i : Nat,∀ hi : i<10,ExtractedMaskCallerModel.CanonicalQM
      (ExtractedMaskLinearLoop.pointAtNat (mapArray point) i hi))
    (g_canonical : FIp_SemanticValues.Canon g) : ∃ out,FIp_SemanticArithmetic.mask c1 maskOnly g point=ok out ∧
    FIp_SemanticValues.Canon out ∧
    FIp_SemanticValues.decode out=FIp_MaskValue.value c1 maskOnly g point := by
  obtain ⟨native,call,canonical,value⟩ := ExtractedMaskCallerModel.selected_mask_value_populated_model
    (mapArray c1) (mapArray maskOnly) (toProbe g) (mapArray point)
    c1_canonical maskOnly_canonical point_canonical g_canonical
  refine ⟨fromProbe native,?_,?_,?_⟩
  · unfold FIp_SemanticArithmetic.mask
    rw [call]
    rfl
  · simpa only [FIp_SemanticValues.Canon,FIp_SemanticValues.to_from] using canonical
  · simpa only [FIp_SemanticValues.decode,FIp_SemanticValues.to_from,FIp_MaskValue.value] using value

#print axioms source
end AspisR1.JFu_MaskBridge
end
