from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
plan=[
 ('NIW_AlignPairInstalled','NJU_WeakPairInstalled',['source'],'slice-d-pair7-20261107'),
 ('NIW_AlignFinishComposedLog','NJU_WeakFinishComposedLog',['source'],'slice-d-pair7-20261107'),
 ('NJF_FinishObserved','NJU_WeakFinishObserved',['detail_source','source','source_log'],'slice-d-pair8-20261107')]
replacements={
 'NIT_PairDomain.Domain':'NJU_WeakPairDomain.Domain',
 'NIG_FinishInput.Domain':'NJU_FinishInput.Holds',
 'NIT_PairDomain.caller':'NJU_WeakPairCaller.caller',
 'NIW_AlignPairPhaseSource.source':'NJU_WeakAlignPairPhaseSource.source',
 'NIW_AlignPairInstalled.source':'NJU_WeakPairInstalled.source',
 'NJF_PairInstantiation.source':'NJU_WeakPairInstantiation.source',
 'NIW_AlignFinishComposedLog.source':'NJU_WeakFinishComposedLog.source'}
for old,new,names,folder in plan:
 source=subprocess.check_output(['git','show','HEAD:'+f'evidence/{folder}/{old}.lean'],text=True);blocks=[]
 for name in names:
  m=re.search(r'^theorem '+name+r'\b',source,re.M);tail=source[m.start():];stop=re.search(r'\n(?:theorem |def |inductive |structure |#print|end )',tail);block=tail[:stop.start()] if stop else tail
  for a,b in replacements.items():block=block.replace(a,b)
  if old=='NJF_FinishObserved':block=block.replace('[detail_source ', '[NJU_WeakFinishObserved.detail_source ')
  blocks.append(block)
 imports=[old,'NJU_WeakPairCaller','NJU_WeakPairInstantiation']
 if old!='NIW_AlignPairInstalled':imports+=['NJU_WeakPairInstalled']
 if old=='NJF_FinishObserved':imports+=['NJU_WeakFinishComposedLog']
 text=''.join('import '+m+'\n' for m in imports)+'set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.'+new+'\n'
 text+=''.join('open '+x+'\n' for x in re.findall(r'^open (.+)$',source,re.M))+'open '+old+'\n'
 text+='\n/- Generalized existing evaluator on arbitrary raw words; data/log definitions reused. -/\n'+'\n\n'.join(blocks)+'\n'
 text+=''.join('#print axioms '+n+'\n' for n in names)+'end AspisR1.'+new+'\n'
 (E/(new+'.lean')).write_text(text)
