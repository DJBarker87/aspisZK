import JFu_MaskTotal
import JGb_Terminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_MaskModel
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic FIp_SemanticValues

theorem source (c1 : Array MQ 16#usize) (maskOnly point : Array MQ 10#usize) (g : MQ)
    (hc1 : ∀ j : Fin 16,ExtractedMaskCallerModel.CanonicalQM (ExtractedMaskCoefficientStep.c1Cell (mapArray c1) j))
    (hm1 : ∀ j : Fin 10,ExtractedMaskCallerModel.CanonicalQM (ExtractedMaskCoefficientStep.maskCell (mapArray maskOnly) j))
    (hp1 : ∀ i : Nat,∀ hi : i<10,ExtractedMaskCallerModel.CanonicalQM (ExtractedMaskLinearLoop.pointAtNat (mapArray point) i hi))
    (hg1 : Canon g) :
    ∃ out,FIp_SemanticArithmetic.mask c1 maskOnly g point=ok out ∧
      Canon out ∧ decode out=FIp_MaskValue.value c1 maskOnly g point := by
  obtain ⟨out,call,hc,hv⟩ := ExtractedMaskCallerModel.selected_mask_value_populated_model
    (mapArray c1) (mapArray maskOnly) (toProbe g) (mapArray point)
    hc1 hm1 hp1 hg1
  refine ⟨fromProbe out,?_,?_,?_⟩
  · unfold FIp_SemanticArithmetic.mask
    rw [call]
    rfl
  · simpa only [Canon,to_from] using hc
  · change ExtractedMaskQM31Exact.decode out = _
    unfold FIp_MaskValue.value
    exact hv
#print axioms source
end AspisR1.JGb_MaskModel
end
