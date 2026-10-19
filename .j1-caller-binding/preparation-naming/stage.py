from pathlib import Path
from datetime import datetime,timezone
import importlib.util,json,sys
B=Path('/home/dombarker/project-offloads');mode=sys.argv[1]
assert mode in ['original','adapted']
w=B/('aspis-r1-public-preparation-20261016/proofs-naming-'+mode)
spec=importlib.util.spec_from_file_location('runner',w/'runner.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
prior=B/'aspis-r1-caller-binding-20261016'
base=prior/'external-inputs-binding.json';data,_=r.verify_snapshot(base)
projects=[prior,B/'aspis-r1-public-preparation-step-20261016/proofs']
manifests={p:json.loads((p/'sources/SOURCE-MANIFEST.json').read_text()) for p in projects}
owners={n:p for p,m in manifests.items() for n in m['modules']};records=[]
def visit(n):
 if n in data['modules']:return
 p=owners[n];item=manifests[p]['modules'][n];source=p/'sources'/item['stage_as']
 assert r.sha(source)==item['source_sha256'];deps=r.imports(source,implicit_init=True)
 for d in deps:visit(d)
 rp=p/'successful-targets'/(n+'.json');receipt=json.loads(rp.read_text())
 assert receipt['exit_status']==0 and receipt['axioms']['passed']
 assert receipt['key']['source_sha256']==r.sha(source)
 assert receipt['key']['runtime']==data['runtime_files'] and receipt['key']['options']==['-j1','-M0']
 objects=r.object_pins(p/'objects',n,data['olean_header_seal']);assert objects==receipt['objects']
 keys=r.external_keys(data)
 for dep,k in receipt['key']['imports'].items():
  if 'receipt_key' in k:
   dp=owners[dep];dr=json.loads((dp/'successful-targets'/(dep+'.json')).read_text())
   assert k=={'receipt_key':r.digest(dr['key']),'objects':data['modules'][dep]['objects']}
  else:assert k=={'closure_key':keys[dep],'objects':data['modules'][dep]['objects']}
 label='naming_'+str(projects.index(p))
 data['modules'][n]={'root':label,'source':str(source),'source_sha256':r.sha(source),
  'imports':deps,'objects':objects,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}}
 records.append({'module':n,'source_sha256':r.sha(source),'receipt':str(rp),
  'receipt_sha256':r.sha(rp),'receipt_key_sha256':r.digest(receipt['key']),'objects':objects})
visit('ExtractedDecoderPublicBinding')
if mode=='original':visit('AspisR1PublicPreparation.Types')
for i,p in enumerate(projects):
 data['roots'].insert(0,{'name':'naming_'+str(i),'source':str(p/'sources'),'objects':str(p/'objects')})
freeze=w/'input-manifests';freeze.mkdir(exist_ok=True)
for i,(p,m) in enumerate(manifests.items()):
 f=freeze/('project-'+str(i)+'.json');r.dump(f,m);data['provenance_files'][str(f)]=r.sha(f)
f=freeze/'base.json';r.dump(f,json.loads(base.read_text()));data['provenance_files'][str(f)]=r.sha(f)
data['scope']='Original28-tag check or naming-only new common cone; old serializer/raw-codec objects unchanged. No Rust/runtime preservation.'
data['captured_utc']=datetime.now(timezone.utc).isoformat()
r.dump(w/'external-inputs.json',data);r.dump(w/'import-source-audit.json',records)
order=['PublicPreparationDiscriminantAudit'] if mode=='original' else [
 'AspisR1PublicPreparation.Types','PublicPreparationDiscriminantAudit',
 'AspisR1PublicPreparation.Funs','PublicPreparationActualAudit',
 'ExtractedPublicPreparationSuccess','PreparationSerializerJoint']
modules={}
for n in order:
 f=w/'sources'/(n.replace('.','/')+'.lean')
 if n=='AspisR1PublicPreparation.Types':path='lean/bridge-public-preparation-20261016/'+n.replace('.','/')+'.lean'
 elif n in ['AspisR1PublicPreparation.Funs','PublicPreparationActualAudit']:path='lean/extracted-public-preparation-20261016/'+n.replace('.','/')+'.lean'
 else:path='lean/'+n+'.lean'
 modules[n]={'source':'docs/research/100bit-spend-path-20261013/'+path,
  'source_sha256':r.sha(f),'source_revision':'9cf712b0504622c2068ac5948a6244db15071552 plus names-only bridge',
  'imports':r.imports(f),'stage_as':str(f.relative_to(w/'sources')),
  'role':'Original/adapted naming gate; no body edit, old cache unchanged',
  'axiom_requests':{'PublicPreparationDiscriminantAudit':1,'PublicPreparationActualAudit':7,'ExtractedPublicPreparationSuccess':3}.get(n,0)}
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':modules,'topological_order':order,'groups':{}});r.staged(w)
print(json.dumps({'mode':mode,'snapshot_sha256':r.sha(w/'external-inputs.json'),'extensions':len(records),'targets':order},indent=2))
