from pathlib import Path
import hashlib,importlib.util,json,shutil
from datetime import datetime,timezone
w=Path('/home/dombarker/project-offloads/aspis-r1-r18-sampler-20261016/pass')
r17=Path('/home/dombarker/project-offloads/aspis-r1-r18-sampler-20261016/models')
c=Path('/home/dombarker/project-offloads/aspis-r1-r18-sampler-20261016/proofs')
spec=importlib.util.spec_from_file_location('runner',w/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
base=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted/external-inputs-002.json');data,_=r.verify_snapshot(base);basekeys=r.external_keys(data)
manifest_by_root={p:json.loads((p/'sources/SOURCE-MANIFEST.json').read_text()) for p in [r17,c]}
receipts={};record_origins=[]
def visit(name):
 if name in data['modules']:return
 hits=[p for p,m in manifest_by_root.items() if name in m['modules']];assert len(hits)==1,(name,hits)
 p=hits[0];item=manifest_by_root[p]['modules'][name];source=p/'sources'/item['stage_as']
 assert r.sha(source)==item['source_sha256'];deps=r.imports(source,implicit_init=True)
 for dep in deps:visit(dep)
 rp=p/'successful-targets'/(name+'.json');receipt=json.loads(rp.read_text())
 assert receipt['exit_status']==0 and receipt['axioms']['passed'],name
 assert receipt['key']['source_sha256']==r.sha(source)
 assert receipt['key']['runtime']==data['runtime_files'];assert receipt['key']['options']==['-j1','-M0']
 objects=r.object_pins(p/'objects',name,data['olean_header_seal']);assert objects==receipt['objects'],name
 expected={}
 for dep in deps:
  if dep in manifest_by_root[p]['modules']:
   dp=p/'successful-targets'/(dep+'.json');dr=json.loads(dp.read_text())
   expected[dep]={'receipt_key':r.digest(dr['key']),'objects':r.object_pins(p/'objects',dep,data['olean_header_seal'])}
  else:
   assert dep in basekeys,dep
   expected[dep]={'objects':data['modules'][dep]['objects'],'closure_key':basekeys[dep]}
 assert receipt['key']['imports']==expected,name
 rootname='r17_checked' if p==r17 else 'sampler_generated_checked'
 data['modules'][name]={'root':rootname,'source':str(source),'source_sha256':r.sha(source),'imports':deps,'objects':objects,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}}
 record_origins.append({'module':name,'source_sha256':r.sha(source),'receipt':str(rp),'receipt_sha256':r.sha(rp),'receipt_key_sha256':r.digest(receipt['key']),'objects':objects})
for name in ['R1SamplerWordPass','AspisR1Qm31SamplerIndex.Funs']:visit(name)
for p,n in [(r17,'r17_checked'),(c,'sampler_generated_checked')]:
 data['roots'].insert(0,{'name':n,'source':str(p/'sources'),'objects':str(p/'objects')})
data['provenance_files'][str(base)]=r.sha(base)
for p in manifest_by_root:data['provenance_files'][str(p/'sources/SOURCE-MANIFEST.json')]=r.sha(p/'sources/SOURCE-MANIFEST.json')
data['scope']='Read/hash extension of pinned R17 external snapshot by 7 successful exact-source/runtime/import/object receipts. No source or object modification, no Lean replay.'
data['captured_utc']=datetime.now(timezone.utc).isoformat()
r.dump(w/'external-inputs-pass.json',data)
r.dump(w/'import-source-audit.json',record_origins)
name='ExtractedQM31SamplerPass';source=w/'sources'/(name+'.lean')
item={'source':'docs/research/100bit-spend-path-20261013/lean/'+name+'.lean','source_sha256':r.sha(source),'source_revision':'c6bc7dff9961632c60676d32f349ba2ccce39614 plus new owned proof','imports':r.imports(source),'stage_as':name+'.lean','role':'Actual emitted sampler division body','axiom_requests':3}
m={'format':2,'modules':{name:item},'topological_order':[name],'groups':{}}
r.dump(w/'sources/SOURCE-MANIFEST.json',m);r.staged(w)
print(json.dumps({'extension_count':len(record_origins),'snapshot_sha256':r.sha(w/'external-inputs-pass.json'),'source_sha256':r.sha(source),'target':name},indent=2))
