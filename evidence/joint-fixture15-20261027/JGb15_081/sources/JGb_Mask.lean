import JFu_MaskTotal
import JGb_Terminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_Mask
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic FIp_SemanticValues
open JFu_MaskInputs

theorem source : ∃ out,FIp_SemanticArithmetic.mask c1 maskOnly g point=ok out ∧
    Canon out ∧ decode out=FIp_MaskValue.value c1 maskOnly g point := by
  obtain ⟨out,call,hc,hv⟩ := ExtractedMaskCallerModel.selected_mask_value_populated_model
    (mapArray c1) (mapArray maskOnly) (toProbe g) (mapArray point)
    c1_canonical maskOnly_canonical point_canonical g_canonical
  refine ⟨fromProbe out,?_,?_,?_⟩
  · unfold FIp_SemanticArithmetic.mask
    rw [call]
    rfl
  · simpa only [Canon,to_from] using hc
  · exact hv
#print axioms source
end AspisR1.JGb_Mask
end
