from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]
s=(p/'lean/FIq_Native10.lean').read_text().split('def pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption\n')[1].split('/-- [')[0]
body=s.split('  := do\n')[1]
lets=re.findall(r'  let (.*?) ←\s*(.*?)(?=\n  let |\n  ok )',body,re.S)
for n,e in lets: print(n,'::',' '.join(e.split()))
header='''import FIx_ScheduleModel
import FIx_ScheduleIndices
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
  lines+=['  have s_same : s=FIx_ScheduleModel.nodeRanges  := (Result.ok.inj h_s).symm','  rw [s_same] at h_nodes']
 elif n=='nodes':
  lines+=['  have v_nodes := FIx_HighSum.value selectors FIx_ScheduleModel.nodeRanges nodes FIx_ScheduleIndices.node_bounds hh h_nodes','  have cv_nodes := v_nodes.1','  have vv_nodes : decode nodes=FIx_ScheduleModel.nodes selectors := v_nodes.2'];vals.append('vv_nodes')
 elif 'initial_variant_selectors' in e:
  lines+=['  obtain ⟨cv_transfer_first,cv_fixed,cv_private_chunk_eight,cv_private_chunk_two,v_variant⟩ :=','    FIx_InitialVariant.value public1.variant q6 q7 q8 (transfer_first,fixed,private_chunk_eight,private_chunk_two) cv_q6 cv_q7 cv_q8 h_variant']
  for vn,proj in [('transfer_first','.1'),('fixed','.2.1'),('private_chunk_eight','.2.2.1'),('private_chunk_two','.2.2.2')]:
   lines.append(f'  have vv_{vn} := congrArg (fun t : K × K × K × K=>t{proj}) v_variant'); lines.append(f'  dsimp only at vv_{vn}'); vals.append('vv_'+vn)
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
  lines += ['  have vi : i.val=9 := FIx_ScheduleIndices.rate_plus_one i h_i']
 elif e.startswith('Array.index_usize initial'):
  _,a,ix=e.split();bound='FIx_ScheduleIndices.rate_bound' if ix=='poseidon2.RATE' else 'FIx_ScheduleIndices.nine_bound i vi'
  lines += [f'  have cv_{n} := FIv_NativeArray.canonical {a} {ix} {n} cv_{a} h_{n}',f'  have vv_{n} := FIw_ArrayReadValue.read {a} {ix} ({bound}) {n} h_{n}'];vals.append('vv_'+n)
 elif e.startswith('Array.update '):
  _,a,ix,x=e.split();bound='FIx_ScheduleIndices.rate_bound' if ix=='poseidon2.RATE' else 'FIx_ScheduleIndices.nine_bound i vi'
  lines += [f'  have v_{n} := FIw_ArrayValue.update {a} {n} {ix} {x} ({bound}) cv_{a} cv_{x} h_{n}',f'  have cv_{n} := v_{n}.1',f'  have vv_{n} := v_{n}.2'];vals.append('vv_'+n)
 elif n=='absorption':
  lines += ['  have v_absorption := FIx_AbsorptionArray.value q38 fixed chunk_two1 chunk_eight1 nodes openings.z absorption','    cv_q38 cv_fixed cv_chunk_two1 cv_chunk_eight1 cv_nodes hz h_absorption','  have vv_absorption := FIx_ArrayMeaning.decoded_of_map absorption _ v_absorption.2'];vals.append('vv_absorption')
 else:raise Exception((n,e))
lines += ['  refine ⟨cv_initial2,v_absorption.1,?_,?_⟩','  · rw [vv_initial2,vv_initial1,vv_initial]','    simp only ['+','.join(vals[::-1])+',vi,poseidon2.RATE,spend.DOMAIN_OWNER_KEY,spend.DOMAIN_NOTE,spend.DOMAIN_NULLIFIER]','    unfold FIx_ScheduleModel.initial FIx_ScheduleModel.initialRaw FIx_ScheduleModel.fullRate FIx_ScheduleModel.full FIx_ScheduleModel.domain FIx_ScheduleModel.length FIx_ScheduleModel.noteFirst FIx_ScheduleModel.firstCommon FIx_ScheduleModel.variant','    funext j','    simp only [Function.update_apply]','    norm_num only', '    split_ifs <;> first | contradiction | rfl','  · rw [vv_absorption]','    simp only ['+','.join(vals[::-1])+']','    unfold FIx_ScheduleModel.absorption FIx_ScheduleModel.chunkEight FIx_ScheduleModel.chunkTwo FIx_ScheduleModel.variant','    rfl','#print axioms value','end AspisR1.FIx_ScheduleValue','end','']
(p/'lean/FIx_ScheduleValue.lean').write_text(header+'\n'.join(lines))
# Replace the large array-write simplification with isolated scalar equalities
# and the checked two-write algebra lemma. No recurrence is normalized.
text=header+'\n'.join(lines)
text=text.replace('import FIx_InitialArray','import FIx_InitialWrites\nimport FIx_InitialArray')
cut=text.index('  refine ⟨cv_initial2,v_absorption.1,?_,?_⟩')
scalar=[v for v in vals[::-1] if v not in ['vv_absorption','vv_initial2','vv_q27','vv_q26','vv_q25','vv_initial1','vv_q24','vv_q23','vv_q22','vv_initial']]
all_defs=['initialRaw','fullRate','full','domain','length','noteFirst','firstCommon','variant','chunkEight','chunkTwo']
end=[]
for a,b in [('full_initial_selector','full'),('q12','fullRate'),('domain','domain'),('length','length'),('chunk_eight1','chunkEight'),('chunk_two1','chunkTwo')]:
 end += [f'  have math_{a} : decode {a}=FIx_ScheduleModel.{b} public1.variant selectors := by', '    simp only ['+','.join(scalar)+']', '    simp only ['+','.join('FIx_ScheduleModel.'+x for x in all_defs[1:])+',spend.DOMAIN_OWNER_KEY,spend.DOMAIN_NOTE,spend.DOMAIN_NULLIFIER]', '    rfl']
end += ['  have math_fixed : decode fixed=(FIx_ScheduleModel.variant public1.variant selectors).2.1 := by','    rw [vv_fixed,vv_q6,vv_q7,vv_q8]','    rfl','  have math_raw : decoded initial=FIx_ScheduleModel.initialRaw public1.variant selectors openings := by','    rw [vv_initial,math_q12,math_full_initial_selector]','    rfl','  refine ⟨cv_initial2,v_absorption.1,?_,?_⟩','  · rw [vv_initial2,vv_q27,vv_q26,vv_q25,vv_initial1,vv_q24,vv_q23,vv_q22,','      FIx_InitialWrites.nine_fin i vi,FIx_InitialWrites.rate_fin,math_raw,math_domain,math_length,vv_q9]','    exact FIx_InitialWrites.value (FIx_ScheduleModel.initialRaw public1.variant selectors openings)','      (low selectors 0) (FIx_ScheduleModel.domain public1.variant selectors)','      (FIx_ScheduleModel.length public1.variant selectors)','  · rw [vv_absorption,math_chunk_two1,math_chunk_eight1,math_fixed,vv_nodes,vv_q38]','    rfl','#print axioms value','end AspisR1.FIx_ScheduleValue','end','']
(p/'lean/FIx_ScheduleValue.lean').write_text(text[:cut]+'\n'.join(end))
