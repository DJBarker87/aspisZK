"""Generate isolated finite-mask facts and symbolic active-loop success.
Only literal table membership is reduced; all field arithmetic uses named laws.
"""
from pathlib import Path
import re,sys
L=Path('evidence/pv-b3p6-20261028/lean')
s=(L/'PV_B3P_E227_05.lean').read_text();masks=[int(x)for x in re.findall(r'(\d+)#u16',s)];assert len(masks)==64
allowed=[1749,2048,2049,4097,6144,6145,26214]
out=['import PV_B3P_Success227','import PV_B3P_E227_14','import PV_B3P_Offset226V3','namespace PV_B3P_Success227','open Aeneas Aeneas.Std PV_B3P_227','set_option autoImplicit false','',
'def MaskAllowed (m : U16) : Prop := '+ ' ∨ '.join('m='+str(m)+'#u16'for m in allowed),'',
'''theorem active_masks_allowed (m : U16)
    (hm : m ∈ reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val) : MaskAllowed m := by
  unfold reference_copy_terminal.constants.ACTIVE_ROW_MASKS at hm
  change m ∈ ['''+', '.join(str(m)+'#u16'for m in masks)+'''] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with '''+' | '.join('h'+str(i)for i in range(64))]
for i,m in enumerate(masks):
 proof='h'+str(i)
 j=allowed.index(m)
 if j<len(allowed)-1:proof='Or.inl '+proof
 for _ in range(j):proof='Or.inr ('+proof+')'
 out+=['  · exact '+proof]
out+=['','#print axioms active_masks_allowed','',
'''theorem mask_sum_total (values : Array aspis_core.field.QM31 16#usize) (mask : U16)
    (hm : MaskAllowed mask) : Success (reference_copy_terminal.selector_mask_sum_16 values mask) := by
  rcases hm with '''+' | '.join('h'+str(i)for i in range(7))]
s=(L/'PV_B3P_E227_12.lean').read_text()
for i,m in enumerate(allowed):
 body=s.split('| '+str(m)+'#uscalar =>',1)[1].split('\n  |',1)[0].strip()
 lets=re.findall(r'let (\w+) ← (.*)',body);tail=body.split('\n')[-1].strip()
 out+=['  · subst mask','    simp only [reference_copy_terminal.selector_mask_sum_16]']
 for name,expr in lets:
  rule='apply index <;> scalar_tac'if expr.startswith('Array.index_usize')else 'apply qadd'
  out+=['    apply bind','    · '+rule,'    intro '+name]
 out+=['    apply qadd']
out+=['','#print axioms mask_sum_total','',
'''theorem active_block_total (selectors : reference_copy_terminal.Selectors)
    (block : Usize) (sum : aspis_core.field.QM31) (hb : block.val<64) :
    Success (reference_copy_terminal.active_block227 selectors block sum) := by
  have hlen : block.val < reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val.length := by
    rw [reference_copy_terminal.constants.ACTIVE_ROW_MASKS.property]
    exact hb
  let mask := reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val[block.val]'hlen
  have hm : MaskAllowed mask := active_masks_allowed mask (List.getElem_mem hlen)
  have hread := PV_B3P_SelectIndex227.index_value
    reference_copy_terminal.constants.ACTIVE_ROW_MASKS block hb
  unfold reference_copy_terminal.active_block227
  rw [hread]
  by_cases hz : mask != 0#u16
  · simp only [show reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val[block.val]'hlen=mask from rfl,
      hz,↓reduceIte]
    apply bind
    · exact index selectors.high block hb
    intro high
    apply bind
    · exact mask_sum_total selectors.low mask hm
    intro low
    apply bind
    · exact qmul high low
    intro product
    exact qadd sum product
  · simp only [show reference_copy_terminal.constants.ACTIVE_ROW_MASKS.val[block.val]'hlen=mask from rfl,
      hz,↓reduceIte]
    exact ok sum

#print axioms active_block_total

theorem active_loop_total (selectors : reference_copy_terminal.Selectors)
    (sum : aspis_core.field.QM31) (block : Usize) (hb : block.val≤64) :
    Success (reference_copy_terminal.Selectors.active_literal_loop selectors sum block) := by
  unfold reference_copy_terminal.Selectors.active_literal_loop
  refine loop_total _ (fun x : aspis_core.field.QM31 × Usize => 64-x.2.val)
    (fun x => x.2.val≤64) ?_ (sum,block) hb
  rintro ⟨acc,i⟩ hi
  change i.val≤64 at hi
  by_cases hp : i.val<64
  · have hb : i<64#usize := by scalar_tac
    obtain ⟨next,hnext⟩ := active_block_total selectors i acc hp
    let j := Usize.wrapping_add i 1#usize
    have hj : j.val=i.val+1 := PV_B3P_Offset226V3.add_value i 1#usize (by
      have hsize := Usize.cMax_bound_concrete.1
      rw [UScalar.size_def]
      scalar_tac)
    refine ⟨.cont (next,j),?_,?_,?_⟩
    · simp only [reference_copy_terminal.Selectors.active_literal_loop.body,hb,↓reduceIte,
        hnext,lift,bind_tc_ok,j]
    · change j.val≤64
      omega
    · change 64-j.val<64-i.val
      omega
  · have hb : ¬i<64#usize := by scalar_tac
    refine ⟨.done acc,?_,True.intro⟩
    simp only [reference_copy_terminal.Selectors.active_literal_loop.body,hb,↓reduceIte]

#print axioms active_loop_total

theorem active_total (selectors : reference_copy_terminal.Selectors) :
    Success (reference_copy_terminal.Selectors.active selectors) :=
  active_loop_total selectors aspis_core.field.QM31.ZERO 0#usize (by change 0≤64; omega)

#print axioms active_total
end PV_B3P_Success227
''']
data='\n'.join(out);p=L/'PV_B3P_ActiveSuccess227.lean'
if '--check'in sys.argv:assert p.read_text()==data
else:p.write_text(data)
