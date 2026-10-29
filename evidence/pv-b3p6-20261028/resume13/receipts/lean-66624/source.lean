import PV_B3P_MaskCallerDomain13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227 PV_B3P_Binding11227
set_option autoImplicit false
noncomputable section
/-- Explicit contextual adapter. It is NOT the total native helper: it keeps
native source behavior on every actual caller mask and rejects other masks.
The unrestricted Link definition is left byte-identical. -/
def frozen_mask_adapter13 (values : Array aspis_core.field.QM31 16#usize) (mask : U16) :
    Result aspis_core.field.QM31 :=
  if MaskAllowed mask then source_mask11 values mask else .fail .panic

theorem owned_mask_outside13 (values : Array aspis_core.field.QM31 16#usize)
    (mask : U16) (outside : ¬ MaskAllowed mask) :
    reference_copy_terminal.selector_mask_sum_16 values mask = .fail .panic := by
  unfold reference_copy_terminal.selector_mask_sum_16
  split <;> try rfl
  all_goals
    exfalso
    apply outside
    simp_all only [MaskAllowed]

theorem frozen_mask_adapter_binding13 (values : Array aspis_core.field.QM31 16#usize) (mask : U16) :
    frozen_mask_adapter13 values mask = reference_copy_terminal.selector_mask_sum_16 values mask := by
  unfold frozen_mask_adapter13
  by_cases h : MaskAllowed mask
  · rw [if_pos h]
    exact (frozen_mask_source11 values mask h).symm
  · rw [if_neg h,owned_mask_outside13 values mask h]

theorem frozen_mask_adapter_link13 :
    PV_B3P_Links13227.PV_B3P_Link_copy_selector_mask_sum_16 frozen_mask_adapter13 :=
  funext (fun values => funext (frozen_mask_adapter_binding13 values))

/-- The adapter changes no call at a frozen-mask caller, for arbitrary data. -/
theorem frozen_mask_caller_transport13 (values : Array aspis_core.field.QM31 16#usize)
    (mask : U16) (member : mask ∈ reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val) :
    frozen_mask_adapter13 values mask = source_mask11 values mask := by
  unfold frozen_mask_adapter13
  exact if_pos (active_masks_allowed mask member)

#print axioms owned_mask_outside13
#print axioms frozen_mask_adapter_binding13
#print axioms frozen_mask_adapter_link13
#print axioms frozen_mask_caller_transport13
end
end PV_B3P_Binding13227
