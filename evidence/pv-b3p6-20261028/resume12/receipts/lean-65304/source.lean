import PV_B3P_CopyMaskSource11227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Success227
set_option autoImplicit false

def active_block_source11 (selectors : reference_copy_terminal.Selectors) (block : Usize) (sum : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let mask ← Array.index_usize reference_copy_terminal.constants.ACTIVE_ROW_MASKS block
  if mask != 0#u16 then
    let high ← Array.index_usize selectors.high block
    let low ← source_mask11 selectors.low mask
    let product ← aspis_core.field.QM31.mul high low
    aspis_core.field.QM31.add sum product
  else .ok sum

attribute [local irreducible] reference_copy_terminal.selector_mask_sum_16 source_mask11 aspis_core.field.QM31.mul aspis_core.field.QM31.add Array.index_usize

theorem active_block_source_binding11 (selectors : reference_copy_terminal.Selectors) (block : Usize)
    (sum : aspis_core.field.QM31) (hb : block.val<64) :
    reference_copy_terminal.active_block227 selectors block sum = active_block_source11 selectors block sum := by
  have hlen : block.val < reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val.length := by
    rw [reference_copy_terminal.constants.ACTIVE_ROW_MASKS.property]
    exact hb
  let mask := reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val[block.val]'hlen
  have hm : MaskAllowed mask := active_masks_allowed mask (List.getElem_mem hlen)
  have hread := PV_B3P_SelectIndex227.index_value reference_copy_terminal.constants.ACTIVE_ROW_MASKS block hb
  have binding := frozen_mask_source11 selectors.low mask hm
  unfold reference_copy_terminal.active_block227 active_block_source11
  rw [hread]
  simp only [bind_tc_ok]
  change (if mask != 0#u16 then _ else _) = (if mask != 0#u16 then _ else _)
  by_cases hz : mask != 0#u16
  · simp only [hz,↓reduceIte,binding]
  · simp only [hz,↓reduceIte]
#print axioms active_block_source_binding11
end PV_B3P_Binding11227
