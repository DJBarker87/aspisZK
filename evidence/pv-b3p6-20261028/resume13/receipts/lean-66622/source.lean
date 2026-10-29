import PV_B3P_LinkDefinitions13227
import PV_B3P_CopyMaskSource11227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding11227
set_option autoImplicit false

/-- A zero mask is a normal return in the deployed source: count_ones=0,
complement=false, initial sum=ZERO, and the while body is skipped. -/
theorem source_mask_zero13 (values : Array aspis_core.field.QM31 16#usize) :
    source_mask11 values 0#u16 = .ok aspis_core.field.QM31.ZERO := rfl

/-- The owned helper deliberately rejects every mask outside seven frozen
nonzero cases. This is a small matcher check, not field normalization. -/
theorem owned_mask_zero13 (values : Array aspis_core.field.QM31 16#usize) :
    reference_copy_terminal.selector_mask_sum_16 values 0#u16 = .fail .panic := rfl

/-- ANY source function with the actual source's zero-mask behavior refutes
our proposed unrestricted Link. The Link definition is retained unchanged. -/
theorem no_total_mask_link13
    (source_model : Array aspis_core.field.QM31 16#usize → U16 → Result aspis_core.field.QM31)
    (values : Array aspis_core.field.QM31 16#usize)
    (source_zero : source_model values 0#u16 = .ok aspis_core.field.QM31.ZERO) :
    ¬ PV_B3P_Links13227.PV_B3P_Link_copy_selector_mask_sum_16 source_model := by
  intro binding
  have h := congrArg (fun operation => operation values 0#u16) binding
  rw [source_zero,owned_mask_zero13] at h
  cases h

theorem mask_model_link_refuted13 (values : Array aspis_core.field.QM31 16#usize) :
    ¬ PV_B3P_Links13227.PV_B3P_Link_copy_selector_mask_sum_16 source_mask11 :=
  no_total_mask_link13 source_mask11 values (source_mask_zero13 values)

#print axioms source_mask_zero13
#print axioms owned_mask_zero13
#print axioms no_total_mask_link13
#print axioms mask_model_link_refuted13
end PV_B3P_Binding13227
