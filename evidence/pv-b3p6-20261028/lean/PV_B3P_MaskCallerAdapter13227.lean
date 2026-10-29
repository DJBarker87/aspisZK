import PV_B3P_MaskAdapter13227
import PV_B3P_CopyActiveLoop12227
import PV_B3P_RangeBinding13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Success227 Result
set_option autoImplicit false
abbrev MaskOperation13 := Array aspis_core.field.QM31 16#usize → U16 → Result aspis_core.field.QM31

def active_block_with13 (operation : MaskOperation13) (selectors : reference_copy_terminal.Selectors)
    (block : Usize) (sum : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let mask ← Array.index_usize reference_copy_terminal.constants.ACTIVE_ROW_MASKS block
  if mask != 0#u16 then
    let high ← Array.index_usize selectors.high block
    let low ← operation selectors.low mask
    let product ← aspis_core.field.QM31.mul high low
    aspis_core.field.QM31.add sum product
  else .ok sum

theorem active_block_source_shape13 (selectors : reference_copy_terminal.Selectors)
    (block : Usize) (sum : aspis_core.field.QM31) :
    active_block_with13 source_mask11 selectors block sum = active_block_source11 selectors block sum := rfl

attribute [local irreducible] aspis_core.field.QM31.mul aspis_core.field.QM31.add
  source_mask11 frozen_mask_adapter13 Array.index_usize

theorem active_block_adapter_transport13 (selectors : reference_copy_terminal.Selectors)
    (block : Usize) (sum : aspis_core.field.QM31) (bound : block.val < 64) :
    active_block_with13 frozen_mask_adapter13 selectors block sum =
      active_block_with13 source_mask11 selectors block sum := by
  let mask := reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val[block.val]'(by
    rw [reference_copy_terminal.constants.ACTIVE_ROW_MASKS.property]; exact bound)
  have member : mask ∈ reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val := List.getElem_mem _
  have read := PV_B3P_SelectIndex227.index_value reference_copy_terminal.constants.ACTIVE_ROW_MASKS block bound
  unfold active_block_with13
  rw [read]
  simp only [bind_tc_ok]
  have transport := frozen_mask_caller_transport13 selectors.low mask member
  dsimp only [mask] at transport
  rw [transport]

def active_step_with13 (operation : MaskOperation13) (selectors : reference_copy_terminal.Selectors)
    (sum : aspis_core.field.QM31) (block : Usize) : Result aspis_core.field.QM31 :=
  active_block_with13 operation selectors block sum

theorem active_body_adapter_transport13 (selectors : reference_copy_terminal.Selectors)
    (state : aspis_core.field.QM31 × Usize) :
    usize_body (active_step_with13 frozen_mask_adapter13 selectors) 64#usize state =
      usize_body (active_step_with13 source_mask11 selectors) 64#usize state := by
  unfold usize_body
  by_cases guard : state.2 < 64#usize
  · have bound : state.2.val < 64 := by scalar_tac
    simp only [guard,if_pos,active_step_with13,active_block_adapter_transport13 selectors state.2 state.1 bound]
  · simp only [guard,if_false]

def source_active_with13 (operation : MaskOperation13) (selectors : reference_copy_terminal.Selectors) :
    Result aspis_core.field.QM31 :=
  range_loop13 (active_step_with13 operation selectors) 0#usize 64#usize aspis_core.field.QM31.ZERO

theorem active_source_adapter_transport13 (selectors : reference_copy_terminal.Selectors) :
    source_active_with13 frozen_mask_adapter13 selectors = source_active_with13 source_mask11 selectors := by
  unfold source_active_with13
  rw [range_loop_binding13,range_loop_binding13]
  have bodies := funext (active_body_adapter_transport13 selectors)
  exact congrArg (fun body => loop body (aspis_core.field.QM31.ZERO,0#usize)) bodies

theorem source_active_binding13 (selectors : reference_copy_terminal.Selectors) :
    source_active_with13 source_mask11 selectors = reference_copy_terminal.Selectors.active_literal selectors := by
  unfold source_active_with13
  rw [range_loop_binding13]
  change _ = reference_copy_terminal.Selectors.active_literal_loop selectors _ _
  rw [active_loop_binding12]
  have steps : active_step_with13 source_mask11 selectors = active_step12 selectors := by
    funext sum block
    exact active_block_source_shape13 selectors block sum
  rw [steps]

theorem active_adapter_link13 :
    PV_B3P_Links13227.PV_B3P_Link_copy_active_literal (source_active_with13 frozen_mask_adapter13) := by
  funext selectors
  exact (active_source_adapter_transport13 selectors).trans (source_active_binding13 selectors)

#print axioms active_block_source_shape13
#print axioms active_block_adapter_transport13
#print axioms active_body_adapter_transport13
#print axioms active_source_adapter_transport13
#print axioms source_active_binding13
#print axioms active_adapter_link13
end PV_B3P_Binding13227
