#!/usr/bin/env python3
"""Stage C proofs over checked preparation loop cache; no compiler invocation."""
from pathlib import Path
import importlib.util,json,shutil
B=Path('/home/dombarker/project-offloads')
p=B/'aspis-r1-public-preparation-20261016/proofs-loop'
w=B/'aspis-r1-public-binding-followup-20261016'
w.mkdir(exist_ok=True); (w/'sources').mkdir(exist_ok=True)
shutil.copy2(p/'runner.py',w/'runner.py')
spec=importlib.util.spec_from_file_location('runner',w/'runner.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
data,_=r.verify_snapshot(p/'external-inputs-loop.json')
name='ExtractedPreparationSerializerLoop'
receipt=p/'successful-targets'/(name+'.json');green=json.loads(receipt.read_text())
source=p/'sources'/(name+'.lean')
assert green['exit_status']==0 and green['axioms']['passed']
assert green['key']['source_sha256']==r.sha(source)
assert green['objects']==r.object_pins(p/'objects',name,data['olean_header_seal'])
data['modules'][name]={'root':'preparation_loop','source':str(source),'source_sha256':r.sha(source),
 'imports':r.imports(source,implicit_init=True),'objects':green['objects'],
 'build_receipt':{'path':str(receipt),'sha256':r.sha(receipt)}}
data['roots'].insert(0,{'name':'preparation_loop','source':str(p/'sources'),'objects':str(p/'objects')})
data['scope']='Worker C exact preparation serializer/helper and source caller binding; no runtime/custody theorem.'
r.dump(w/'external-inputs.json',data)
mods={}
for s in (w/'sources').glob('*.lean'):
 name=s.stem
 mods[name]={'source':'docs/research/100bit-spend-path-20261013/lean/'+s.name,
  'source_sha256':r.sha(s),'source_revision':'ebe378259 + exact worker C source hash',
  'imports':r.imports(s),'stage_as':s.name,'role':'Worker C focused target',
  'axiom_requests':s.read_text().count('#print axioms')}
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':list(mods),'groups':{}})
r.staged(w)
print('Staged',list(mods),'over',len(data['modules']),'exact pinned inputs; compiler not invoked')
