import PV_B3P_MaskBody10_1749227
import PV_B3P_MaskBody10_2048227
import PV_B3P_MaskBody10_2049227
import PV_B3P_MaskBody10_4097227
import PV_B3P_MaskBody10_6144227
import PV_B3P_MaskBody10_6145227
import PV_B3P_MaskBody10_26214227
import PV_B3P_ActiveSuccess227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Success227
set_option autoImplicit false

def source_mask11 (values : Array aspis_core.field.QM31 16#usize) (mask : U16) : Result aspis_core.field.QM31 :=
  PV_B3P_Mask227.foldResult (mask_step10 values) (PV_B3P_Mask227.walk 16 mask.val) aspis_core.field.QM31.ZERO

theorem frozen_mask_source11 (values : Array aspis_core.field.QM31 16#usize) (mask : U16) (hm : MaskAllowed mask) :
    reference_copy_terminal.selector_mask_sum_16 values mask = source_mask11 values mask := by
  unfold source_mask11
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst mask
    exact mask_body_binding10_1749 values
  · subst mask
    exact mask_body_binding10_2048 values
  · subst mask
    exact mask_body_binding10_2049 values
  · subst mask
    exact mask_body_binding10_4097 values
  · subst mask
    exact mask_body_binding10_6144 values
  · subst mask
    exact mask_body_binding10_6145 values
  · subst mask
    exact mask_body_binding10_26214 values
#print axioms frozen_mask_source11
end PV_B3P_Binding11227
