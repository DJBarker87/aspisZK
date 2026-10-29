import PV_B3P_MaskLinkCounterexample13227
import PV_B3P_CopyActiveSource11227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227 PV_B3P_Binding11227
set_option autoImplicit false

theorem zero_not_allowed13 : ¬ MaskAllowed 0#u16 := by
  intro h
  rcases h with h | h | h | h | h | h | h <;> scalar_tac

/-- A zero mask cannot trigger the helper call in the actual source-shaped
active block. This does not weaken the refuted helper Link. -/
theorem active_zero_guard13 (selectors : reference_copy_terminal.Selectors)
    (block : Usize) (sum : aspis_core.field.QM31)
    (mask_read : Array.index_usize reference_copy_terminal.constants.ACTIVE_ROW_MASKS block = .ok 0#u16) :
    active_block_source11 selectors block sum = .ok sum := by
  unfold active_block_source11
  rw [mask_read]
  rfl

/-- The frozen mask membership proof excludes the counterexample input. -/
theorem frozen_mask_nonzero13 (mask : U16)
    (member : mask ∈ reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val) :
    mask ≠ 0#u16 := by
  have h := active_masks_allowed mask member
  intro zero
  subst mask
  exact zero_not_allowed13 h

#print axioms zero_not_allowed13
#print axioms active_zero_guard13
#print axioms frozen_mask_nonzero13
end PV_B3P_Binding13227
