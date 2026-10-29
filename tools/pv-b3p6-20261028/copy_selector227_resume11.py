"""Bind seven frozen masks universally on their domain, then at actual active-block caller."""
from pathlib import Path
import sys
L=Path('evidence/pv-b3p6-20261028/lean');h='namespace PV_B3P_Binding11227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Success227\nset_option autoImplicit false\n'
masks=[1749,2048,2049,4097,6144,6145,26214]
s=''.join(f'import PV_B3P_MaskBody10_{m}227\n'for m in masks)+'import PV_B3P_ActiveSuccess227\n'+h+'''
def source_mask11 (values : Array aspis_core.field.QM31 16#usize) (mask : U16) : Result aspis_core.field.QM31 :=
  PV_B3P_Mask227.foldResult (mask_step10 values) (PV_B3P_Mask227.walk 16 mask.val) aspis_core.field.QM31.ZERO

theorem frozen_mask_source11 (values : Array aspis_core.field.QM31 16#usize) (mask : U16) (hm : MaskAllowed mask) :
    reference_copy_terminal.selector_mask_sum_16 values mask = source_mask11 values mask := by
  unfold source_mask11
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6
'''
for i,m in enumerate(masks):s+=f'  · subst mask\n    exact mask_body_binding10_{m} values\n'
s+='#print axioms frozen_mask_source11\nend PV_B3P_Binding11227\n'
files={'PV_B3P_CopyMaskSource11227':s}
s='import PV_B3P_CopyMaskSource11227\n'+h+'''
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
''';files['PV_B3P_CopyActiveSource11227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
