"""Generalize theorem statements only; reuse all original definitions/traces."""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
plan=[
 ('NIT_SharedChain',['shared_interpreted'],'slice-d-pair6-20261107'),
 ('NIT_SharedComplete',['complete'],'slice-d-pair6-20261107'),
 ('NIT_RegularChain',['after_interpreted','after_exists','interpreted','complete'],'slice-d-pair6-20261107'),
 ('NIT_AllocatorChain',['interpreted','complete'],'slice-d-pair6-20261107'),
 ('NIW_AlignSharedPhase',['trace'],'slice-d-pair7-20261107'),
 ('NIW_AlignAfterPhase',['trace'],'slice-d-pair7-20261107'),
 ('NIW_AlignRegularPhase',['trace'],'slice-d-pair7-20261107'),
 ('NIW_AlignRegularPhaseSource',['source','frames'],'slice-d-pair7-20261107'),
 ('NIW_AlignAllocatorPhase',['trace','source'],'slice-d-pair7-20261107'),
 ('NIW_AlignPairPhase',['certificate'],'slice-d-pair7-20261107'),
 ('NIW_AlignPairPhaseSource',['source'],'slice-d-pair7-20261107'),
 ('NJF_RegularContinuation',['source'],'slice-d-pair8-20261107'),
 ('NJF_AllocatorInstantiation',['source'],'slice-d-pair8-20261107'),
 ('NJF_PairInstantiation',['source','root'],'slice-d-pair8-20261107')]
newname=lambda old:'NJU_Weak'+old.split('_',1)[1]
replace={old+'.'+n:newname(old)+'.'+n for old,ns,_ in plan for n in ns}
records=[];modules=['NJU_WeakPairDomain']
for old,names,folder in plan:
 path=f'evidence/{folder}/{old}.lean';source=subprocess.check_output(['git','show','HEAD:'+path],text=True)
 ns=newname(old);blocks=[]
 for name in names:
  m=re.search(r'^theorem '+re.escape(name)+r'\b',source,re.M);assert m,(old,name)
  tail=source[m.start():];stop=re.search(r'\n(?:theorem |def |inductive |structure |#print|end )',tail)
  block=tail[:stop.start()] if stop else tail
  block=block.replace('NIT_PairDomain.Domain','NJU_WeakPairDomain.Domain')
  block=block.replace('(NIT_PairDomain.message_size _ _ _ _ domain)','domain.size')
  for a,b in replace.items():block=block.replace(a,b)
  if re.search(r'^def run\b',source,re.M):
   block=re.sub(r'([\[,]\s*)run(?=\s*[,\]])',lambda m:m[1]+old+'.run',block)
  blocks.append(block)
 original_imports=re.findall(r'^import (\S+)',source,re.M)
 deps=[m for m in modules if m+'.' in '\n'.join(blocks) or m=='NJU_WeakPairDomain' or any(newname(o)==m for o in original_imports)]
 text='import '+old+'\n'+''.join('import '+x+'\n' for x in deps)
 text+='set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.'+ns+'\n'
 # Reuse old trace inductives and native/source evaluator definitions verbatim.
 opens=re.findall(r'^open (.+)$',source,re.M)
 text+=''.join('open '+x+'\n' for x in opens)+'open '+old+'\n'
 for original,_,_ in plan:
  if newname(original) in deps and any(original in line.split() for line in opens):text+='open '+newname(original)+'\n'
 if 'variable [FIo_Native.Allocation]' in source:text+='variable [FIo_Native.Allocation]\n'
 text+='\n/- Generalized domain only. Original data/trace/evaluator definitions reused. -/\n'
 text+='\n\n'.join(blocks)+'\n\n'+''.join('#print axioms '+n+'\n' for n in names)+'end AspisR1.'+ns+'\n'
 (E/(ns+'.lean')).write_text(text);modules.append(ns)
 records.append(dict(original=path,sha256=hashlib.sha256(source.encode()).hexdigest(),module=ns,theorems=names,reused_definitions=True,domain_change='drop raw word bounds; retain exact final message length2048'))
(E/'NJU_GENERALIZATION.json').write_text(json.dumps(dict(modules=modules,records=records),indent=2)+'\n')
print(json.dumps(dict(modules=len(modules),new_extractions=0)))
