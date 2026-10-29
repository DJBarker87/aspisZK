import PV_B3P_MaskNative14227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std PV_B3P_Success227
set_option autoImplicit false
/-- Nonempty caller domain and native-shaped helper law hold at once. No
false total helper equality or empty-domain witness is used. -/
theorem source_mask_joint_witness14 :
    ∃ source called, PV_B3P_Link_mask_on_domain source ∧
      PV_B3P_Link_mask_call_domain called ∧ (∃ mask, called mask) := by
  refine ⟨native_mask14,MaskAllowed,native_mask_link14,fun _ member => member,1749#u16,?_⟩
  exact Or.inl rfl
#print axioms source_mask_joint_witness14
end PV_B3P_Correct14227
