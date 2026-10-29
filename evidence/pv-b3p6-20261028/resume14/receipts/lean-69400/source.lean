import PV_B3P_MaskAdapter13227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding11227 PV_B3P_Binding13227 PV_B3P_Success227
set_option autoImplicit false
abbrev MaskFn := Array aspis_core.field.QM31 16#usize → U16 → Result aspis_core.field.QM31
/-- Corrected direct link: the frozen seven-mask domain is essential. -/
def PV_B3P_Link_mask_on_domain (source : MaskFn) : Prop :=
  ∀ values mask, MaskAllowed mask →
    source values mask = reference_copy_terminal.selector_mask_sum_16 values mask
/-- Separate caller obligation; zero table entries skip the helper call. -/
def PV_B3P_Link_mask_call_domain (called : U16 → Prop) : Prop :=
  ∀ mask, called mask → MaskAllowed mask

def frozen_calls14 (mask : U16) : Prop :=
  mask ∈ reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val ∧ mask ≠ 0#u16

theorem mask_direct14 : PV_B3P_Link_mask_on_domain source_mask11 := by
  intro values mask h
  exact (frozen_mask_source11 values mask h).symm

theorem mask_call_domain14 : PV_B3P_Link_mask_call_domain frozen_calls14 := by
  intro mask h
  exact active_masks_allowed mask h.1

theorem mask_at_actual_call14 (source : MaskFn) (called : U16 → Prop)
    (body : PV_B3P_Link_mask_on_domain source)
    (domain : PV_B3P_Link_mask_call_domain called)
    (values : Array aspis_core.field.QM31 16#usize) (mask : U16) (call : called mask) :
    source values mask = reference_copy_terminal.selector_mask_sum_16 values mask :=
  body values mask (domain mask call)

theorem mask_joint_witness14 :
    ∃ source called, PV_B3P_Link_mask_on_domain source ∧
      PV_B3P_Link_mask_call_domain called :=
  ⟨source_mask11,frozen_calls14,mask_direct14,mask_call_domain14⟩
#print axioms mask_direct14
#print axioms mask_call_domain14
#print axioms mask_at_actual_call14
#print axioms mask_joint_witness14
end PV_B3P_Correct14227
