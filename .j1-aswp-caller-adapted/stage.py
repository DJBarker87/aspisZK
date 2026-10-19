from pathlib import Path
import hashlib,importlib.util,json,shutil
from datetime import datetime,timezone
w=Path('/home/dombarker/project-offloads/aspis-r1-j1a-caller-adapted-20261016')
r17=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted')
c=Path('/home/dombarker/project-offloads/aspis-r1-j1a-caller-proof-20261016')
spec=importlib.util.spec_from_file_location('runner',w/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
base=r17/'external-inputs-002.json';data,_=r.verify_snapshot(base);basekeys=r.external_keys(data)
manifest_by_root={r17:json.loads((r17/'sources/SOURCE-MANIFEST.json').read_text())}
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
 rootname='r17_checked' if p==r17 else 'caller_checked'
 data['modules'][name]={'root':rootname,'source':str(source),'source_sha256':r.sha(source),'imports':deps,'objects':objects,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}}
 record_origins.append({'module':name,'source_sha256':r.sha(source),'receipt':str(rp),'receipt_sha256':r.sha(rp),'receipt_key_sha256':r.digest(receipt['key']),'objects':objects})
for name in ['WithdrawalCarrierBridge431']:visit(name)
for p,n in [(r17,'r17_checked')]:
 data['roots'].insert(0,{'name':n,'source':str(p/'sources'),'objects':str(p/'objects')})
data['provenance_files'][str(base)]=r.sha(base)
input_manifests=w/'input-manifests';input_manifests.mkdir(exist_ok=True)
for p in manifest_by_root:
 label='r17' if p==r17 else 'caller'
 target=input_manifests/(label+'.json')
 r.dump(target,manifest_by_root[p])
 data['provenance_files'][str(target)]=r.sha(target)
data['scope']='Read/hash extension of pinned R17 external snapshot by actual successful exact-source/runtime/import/object receipts. No source or object modification, no Lean replay.'
data['captured_utc']=datetime.now(timezone.utc).isoformat()
r.dump(w/'external-inputs-carrier.json',data)
r.dump(w/'import-source-audit.json',record_origins)

mods={}
for name in ['AspisR1WithdrawalCaller.Types','AspisR1WithdrawalCaller.Funs','ExtractedWithdrawalCallerSuccess','WithdrawalCallerDiscriminantAudit','ExtractedWithdrawalCallerCarrier']:
 p=w/'sources'/(name.replace('.','/')+'.lean')
 mods[name]={'stage_as':str(p.relative_to(w/'sources')),'source_sha256':r.sha(p),'imports':r.imports(p),'source_revision':'4418b6ed6 plus new naming adapter/carrier; originalFuns/Success body unchanged','source':('docs/research/100bit-spend-path-20261013/lean/'+p.name),'role':'one-sided Caller namespace and actual validator transport'}
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':list(mods),'groups':{}});r.staged(w)
print(json.dumps({'extension_count':len(record_origins),'snapshot_sha256':r.sha(w/'external-inputs-carrier.json'),'targets':list(mods)},indent=2))
