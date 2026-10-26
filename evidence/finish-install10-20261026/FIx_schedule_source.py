from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]
s=(p/'lean/FIq_Native10.lean').read_text().split('def pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption\n')[1].split('/-- [')[0]
body=s.split('  := do\n')[1]
lets=re.findall(r'  let (.*?) ←\s*(.*?)(?=\n  let |\n  ok )',body,re.S)
for n,e in lets: print(n,'::',' '.join(e.split()))
header='''import FIx_ScheduleModel
import FIx_InitialArray
import FIx_AbsorptionArray
import FIx_ArrayMeaning
import FIw_ScalarArithmetic
import FIw_WordValue
import FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ScheduleValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIx_ScheduleModel (high low)
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

theorem value (public1 : Public) (openings : Openings) (selectors : Selectors)
    (out1 out2 : Array NQ 16#usize)
    (hz : canonical openings.z) (hh : canonical selectors.high) (hl : canonical selectors.low)
    (run : pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption
      public1 openings selectors=ok (out1,out2)) :
    canonical out1 ∧ canonical out2 ∧
      decoded out1=FIx_ScheduleModel.initial public1.variant selectors openings ∧
      decoded out2=FIx_ScheduleModel.absorption public1.variant selectors openings := by
  unfold pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption at run
'''
lines=[]
for n,e in lets:
    if n.startswith('('):lines.append(f'  obtain ⟨⟨{n[1:-1]}⟩,h_variant,run⟩ := FIv_Map.bind_success _ _ _ run')
    else:lines.append(f'  obtain ⟨{n},h_{n},run⟩ := FIv_Map.bind_success _ _ _ run')
lines.append('  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)')
vals=[]
for n,e0 in lets:
 e=' '.join(e0.split())
 if n=='s':
  lines+=['  have s_same : s=FIx_ScheduleModel.nodeRanges := Result.ok.inj h_s','  rw [s_same] at h_nodes']
 elif n=='nodes':
  lines+=['  have v_nodes := FIx_HighSum.value selectors FIx_ScheduleModel.nodeRanges nodes (by','    intro r hr','    simp only [FIx_ScheduleModel.nodeRanges,Array.to_slice,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hr','    rcases hr with rfl | rfl <;> constructor <;> scalar_tac) hh h_nodes','  have cv_nodes := v_nodes.1','  have vv_nodes : decode nodes=FIx_ScheduleModel.nodes selectors := v_nodes.2'];vals.append('vv_nodes')
 elif 'initial_variant_selectors' in e:
  lines+=['  obtain ⟨cv_transfer_first,cv_fixed,cv_private_chunk_eight,cv_private_chunk_two,v_variant⟩ :=','    FIx_InitialVariant.value public1.variant q6 q7 q8 (transfer_first,fixed,private_chunk_eight,private_chunk_two) cv_q6 cv_q7 cv_q8 h_variant']
  for vn,proj in [('transfer_first','.1'),('fixed','.2.1'),('private_chunk_eight','.2.2.1'),('private_chunk_two','.2.2.2')]:
   lines.append(f'  have vv_{vn} := congrArg (fun t : K × K × K × K=>t{proj}) v_variant'); vals.append('vv_'+vn)
 elif e.startswith('Array.index_usize selectors.'):
  _,a,ix=e.split(); suff='hh' if a.endswith('high') else 'hl'; f='high' if a.endswith('high') else 'low'
  lines += [f'  have cv_{n} := FIv_NativeArray.canonical {a} {ix} {n} {suff} h_{n}',f'  have vv_{n} : decode {n}={f} selectors ({ix}).val := (FIv_NativeArray.read {a} {ix} {n} h_{n}).symm'];vals.append('vv_'+n)
 elif e.startswith(('field.QM31.add ','field.QM31.mul ','field.QM31.sub ')):
  op,a,b=e.split(); op=op.rsplit('.',1)[1]; lemma='FIv_SubMap.qm' if op=='sub' else 'FIv_NativeValue.'+op
  lines += [f'  have v_{n} := {lemma} {a} {b} {n} cv_{a} cv_{b} h_{n}',f'  have cv_{n} := v_{n}.1',f'  have vv_{n} := v_{n}.2'];vals.append('vv_'+n)
 elif e.startswith('field.QM31.mul_m31 '):
  _,a,b=e.split();lines += [f'  have v_{n} := FIw_ScalarArithmetic.mul {a} {n} {b} h_{n}',f'  have cv_{n} := v_{n}.1',f'  have vv_{n} := v_{n}.2'];vals.append('vv_'+n)
 elif e.startswith('field.PreparedQm31Multiplier.new '):
  a=e.split()[-1];lines.append(f'  have valid_{n} := FIv_PreparedNew.valid {a} {n} cv_{a} h_{n}')
 elif n=='initial':
  lines += ['  have v_initial := FIx_InitialArray.value q12 full_initial_selector full_or_rate full openings initial','    cv_q12 cv_full_initial_selector valid_full_or_rate valid_full hz h_initial','  have cv_initial := v_initial.1','  have vv_initial := FIx_ArrayMeaning.decoded_of_map initial _ v_initial.2']; vals.append('vv_initial')
 elif n=='i':
  lines += ['  have v_i := FIw_WordValue.add poseidon2.RATE 1#usize i h_i','  have vi : i.val=9 := by rw [poseidon2.RATE] at v_i;scalar_tac']
 elif e.startswith('Array.index_usize initial'):
  _,a,ix=e.split();bound='by rw [poseidon2.RATE];scalar_tac' if ix=='poseidon2.RATE' else 'by rw [vi];scalar_tac'
  lines += [f'  have cv_{n} := FIv_NativeArray.canonical {a} {ix} {n} cv_{a} h_{n}',f'  have vv_{n} := FIw_ArrayReadValue.read {a} {ix} ({bound}) {n} h_{n}'];vals.append('vv_'+n)
 elif e.startswith('Array.update '):
  _,a,ix,x=e.split();bound='by rw [poseidon2.RATE];scalar_tac' if ix=='poseidon2.RATE' else 'by rw [vi];scalar_tac'
  lines += [f'  have v_{n} := FIw_ArrayValue.update {a} {n} {ix} {x} ({bound}) cv_{a} cv_{x} h_{n}',f'  have cv_{n} := v_{n}.1',f'  have vv_{n} := v_{n}.2'];vals.append('vv_'+n)
 elif n=='absorption':
  lines += ['  have v_absorption := FIx_AbsorptionArray.value q38 fixed chunk_two1 chunk_eight1 nodes openings.z absorption','    cv_q38 cv_fixed cv_chunk_two1 cv_chunk_eight1 cv_nodes hz h_absorption','  have vv_absorption := FIx_ArrayMeaning.decoded_of_map absorption _ v_absorption.2'];vals.append('vv_absorption')
 else:raise Exception((n,e))
lines += ['  refine ⟨cv_initial2,v_absorption.1,?_,?_⟩','  · rw [vv_initial2,vv_initial1,vv_initial]','    simp only ['+','.join(vals[::-1])+',vi,poseidon2.RATE,spend.DOMAIN_OWNER_KEY,spend.DOMAIN_NOTE,spend.DOMAIN_NULLIFIER]','    unfold FIx_ScheduleModel.initial FIx_ScheduleModel.initialRaw FIx_ScheduleModel.fullRate FIx_ScheduleModel.full FIx_ScheduleModel.domain FIx_ScheduleModel.length FIx_ScheduleModel.noteFirst FIx_ScheduleModel.firstCommon FIx_ScheduleModel.variant','    funext j','    simp only [Function.update_apply]','    split_ifs <;> rfl','  · rw [vv_absorption]','    simp only ['+','.join(vals[::-1])+']','    unfold FIx_ScheduleModel.absorption FIx_ScheduleModel.chunkEight FIx_ScheduleModel.chunkTwo FIx_ScheduleModel.variant','    rfl','#print axioms value','end AspisR1.FIx_ScheduleValue','end','']
(p/'lean/FIx_ScheduleValue.lean').write_text(header+'\n'.join(lines))
