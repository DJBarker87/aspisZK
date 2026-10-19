from pathlib import Path
from datetime import datetime, timezone
import importlib.util,json
B=Path('/home/dombarker/project-offloads')
w=B/'aspis-r1-public-preparation-20261016/proofs-serializer'
p=B/'aspis-r1-public-preparation-20261016/proofs-original'
spec=importlib.util.spec_from_file_location('runner',w/'runner.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
base=B/'aspis-r1-caller-binding-20261016/external-inputs-binding.json';data,_=r.verify_snapshot(base)
original_keys=r.external_keys(data)
manifest=json.loads((p/'sources/SOURCE-MANIFEST.json').read_text())
records=[]
def visit(name):
 if name in data['modules']:return
 item=manifest['modules'][name];source=p/'sources'/item['stage_as']
 assert r.sha(source)==item['source_sha256']
 deps=r.imports(source,implicit_init=True)
 for dep in deps:visit(dep)
 rp=p/'successful-targets'/(name+'.json');receipt=json.loads(rp.read_text())
 assert receipt['exit_status']==0 and receipt['axioms']['passed'],name
 assert receipt['key']['source_sha256']==r.sha(source)
 assert receipt['key']['runtime']==data['runtime_files']
 assert receipt['key']['options']==['-j1','-M0']
 objects=r.object_pins(p/'objects',name,data['olean_header_seal'])
 assert objects==receipt['objects'],name
 expected={}
 for dep in deps:
  if dep in manifest['modules']:
   dr=json.loads((p/'successful-targets'/(dep+'.json')).read_text())
   expected[dep]={'receipt_key':r.digest(dr['key']),'objects':r.object_pins(p/'objects',dep,data['olean_header_seal'])}
  else:expected[dep]={'closure_key':original_keys[dep],'objects':data['modules'][dep]['objects']}
 assert receipt['key']['imports']==expected,name
 data['modules'][name]={'root':'public_preparation_original','source':str(source),'source_sha256':r.sha(source),'imports':deps,'objects':objects,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}}
 records.append({'module':name,'source_sha256':r.sha(source),'receipt':str(rp),'receipt_sha256':r.sha(rp),'receipt_key_sha256':r.digest(receipt['key']),'objects':objects})
visit('AspisR1PublicPreparation.Funs')
data['roots'].insert(0,{'name':'public_preparation_original','source':str(p/'sources'),'objects':str(p/'objects')})
freeze=w/'input-manifests';freeze.mkdir(exist_ok=True)
for name,value in [('preparation-original',manifest),('base-snapshot',json.loads(base.read_text()))]:
 f=freeze/(name+'.json');r.dump(f,value);data['provenance_files'][str(f)]=r.sha(f)
data['scope']='Exact two original generated modules, imported from their producing receipts; no outer caller reachability or runtime preservation.'
data['captured_utc']=datetime.now(timezone.utc).isoformat()
r.dump(w/'external-inputs-serializer.json',data);r.dump(w/'import-source-audit.json',records)
name='PreparationSerializerJoint';source=w/'sources'/(name+'.lean')
item={'source':'docs/research/100bit-spend-path-20261013/lean/'+name+'.lean','source_sha256':r.sha(source),'source_revision':'f6521c1249cef35b01b2e343445ec795d9ec82eb plus new helper-success proof','imports':r.imports(source),'stage_as':name+'.lean','role':'Joint import diagnostic only; no theorem claim','axiom_requests':0}
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':{name:item},'topological_order':[name],'groups':{}});r.staged(w)
print(json.dumps({'extension_count':len(records),'snapshot_sha256':r.sha(w/'external-inputs-serializer.json'),'source_sha256':r.sha(source)},indent=2))
