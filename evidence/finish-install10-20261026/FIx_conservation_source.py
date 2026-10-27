from pathlib import Path
import re
P=Path(__file__).resolve().parents[2]
s=(P/'lean/FIq_Native09.lean').read_text().split('def pool_v1.pair_forest_semantic_terminal.add_value_lanes\n')[1].split('\n\n\nend FIq_Native')[0]
body=s.split('  := do\n')[1]
lets=re.findall(r'^  let ([^\n]*?) ←\s*(.*?)(?=\n  let |\n  pool_v1.pair_forest_semantic_terminal.add_preweighted packed1)',body,re.S|re.M)
header='''import FIx_ValueConservation
import FIx_ValueBitPrefix
import FIw_SelectorRow
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ValueConservationSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

theorem value (packed out : Array NQ 24#usize) (o : Openings) (s : Selectors)
    (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
    (hh : canonical s.high) (hl : canonical s.low)
    (success : pool_v1.pair_forest_semantic_terminal.add_value_lanes packed o s=ok out) :
    ∃ (before : Array NQ 24#usize) (selector : NQ) (row base : Usize) (scalars : Array NQ 2#usize),
      16#usize*pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK=ok base ∧
      base+6#usize=ok row ∧ pool_v1.pair_forest_copy_terminal.Selectors.row s row=ok selector ∧
      FIx_ValueConservation.run selector o.z o.succ_z=ok scalars ∧
      pool_v1.pair_forest_semantic_terminal.add_preweighted before 82#usize scalars=ok out ∧
      canonical scalars ∧ scalars.val.map decode=FIx_ValueConservation.model
        (FIv_NativeArray.value s.high (row.val/16)*FIv_NativeArray.value s.low (row.val%16))
        (FIv_NativeArray.value o.z) (FIv_NativeArray.value o.succ_z) := by
  unfold pool_v1.pair_forest_semantic_terminal.add_value_lanes at success
'''
lines=[]
for n,e in lets:
 proof=n.strip('()').replace(',','_').replace(' ','')
 if n.startswith('('):lines.append(f'  obtain ⟨⟨{n[1:-1]}⟩,h_{proof},success⟩ := FIv_Map.bind_success _ _ _ success')
 else:lines.append(f'  obtain ⟨{n},h_{proof},success⟩ := FIv_Map.bind_success _ _ _ success')
lines+=['  have finalCall := success','  have zero : canonical (Array.repeat 33#usize field.QM31.ZERO) := by','    intro x hx','    have same : x=field.QM31.ZERO := List.eq_of_mem_replicate hx','    rw [same]','    exact FIv_NativeValue.zero.1',
'  have v0 := FIx_ValueBits0.value 10 0#usize o openings1 _ range1 (by rfl) hz zero h_openings1_range1',
'  have e0 := v0.1','  subst openings1',
'  have v1 := FIx_ValueBits1.value 10 0#usize o openings2 range1 range2 (by rfl) hs v0.2.1 h_openings2_range2',
'  have e1 := v1.1','  subst openings2',
'  have v2 := FIx_ValueBits2.value 10 0#usize o openings3 range2 range3 (by rfl) hx v1.2.1 h_openings3_range3',
'  have e2 := v2.1','  subst openings3',
'  let scalars := Array.make 2#usize [q20,q24]',
'  have scalarCall : FIx_ValueConservation.run conservation_selector o.z o.succ_z=ok scalars := by',
'    simp only [FIx_ValueConservation.run,h_q15,h_q16,h_q17,h_q18,h_q19,h_q20,h_q21,h_q22,h_q23,h_q24,bind_tc_ok]',
'    rfl',
'  have selectorValue := FIw_SelectorRow.value_exact s i3 conservation_selector hh hl h_conservation_selector',
'  have meaning := FIx_ValueConservation.value conservation_selector o.z o.succ_z scalars selectorValue.1 hz hs scalarCall',
'  refine ⟨packed1,conservation_selector,i3,i2,scalars,h_i2,h_i3,h_conservation_selector,scalarCall,finalCall,meaning.1,?_⟩',
'  rw [meaning.2,selectorValue.2]',
'#print axioms value','end AspisR1.FIx_ValueConservationSource','end','']
(P/'lean/FIx_ValueConservationSource.lean').write_text(header+'\n'.join(lines))
print('Native binds:',len(lets))
