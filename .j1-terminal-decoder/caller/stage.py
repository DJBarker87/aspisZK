from pathlib import Path
from datetime import datetime,timezone
import importlib.util,json
B=Path('/home/dombarker/project-offloads')
w=B/'aspis-r1-j1a-terminal-decoder-copy-helper-proof-20261016/caller'
c=B/'aspis-r1-j1a-terminal-decoder-copy-helper-proof-20261016/proofs'
p=B/'aspis-r1-j1a-terminal-public-adapted-20261016'
s=importlib.util.spec_from_file_location('runner',w/'runner.py');r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
base=p/'external-inputs-public.json';data,_=r.verify_snapshot(base)
manifest_by_root={x:json.loads((x/'sources/SOURCE-MANIFEST.json').read_text()) for x in (c,p)}
origin_data={c:r.verify_snapshot(B/'aspis-r1-j17-port-20261015/extracted/external-inputs-002.json')[0],p:data}
origin_keys={x:r.external_keys(d) for x,d in origin_data.items()}
records=[]
def visit(name):
 if name in data['modules']:return
 hits=[x for x,m in manifest_by_root.items() if name in m['modules']];assert len(hits)==1,(name,hits)
 x=hits[0];item=manifest_by_root[x]['modules'][name];source=x/'sources'/item['stage_as'];assert r.sha(source)==item['source_sha256']
 deps=r.imports(source,implicit_init=True)
 for dep in deps:visit(dep)
 rp=x/'successful-targets'/(name+'.json');receipt=json.loads(rp.read_text())
 assert receipt['exit_status']==0 and receipt['axioms']['passed'],name
 assert receipt['key']['source_sha256']==r.sha(source)
 assert receipt['key']['runtime']==data['runtime_files']
 assert receipt['key']['options']==['-j1','-M0']
 objects=r.object_pins(x/'objects',name,data['olean_header_seal']);assert objects==receipt['objects']
 expected={}
 for dep in deps:
  if dep in manifest_by_root[x]['modules']:
   dr=json.loads((x/'successful-targets'/(dep+'.json')).read_text())
   expected[dep]={'receipt_key':r.digest(dr['key']),'objects':r.object_pins(x/'objects',dep,data['olean_header_seal'])}
  else:expected[dep]={'closure_key':origin_keys[x][dep],'objects':origin_data[x]['modules'][dep]['objects']}
 assert receipt['key']['imports']==expected,name
 label='decoder_checked' if x==c else 'public_checked'
 data['modules'][name]={'root':label,'source':str(source),'source_sha256':r.sha(source),'imports':deps,'objects':objects,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}}
 records.append({'module':name,'source_sha256':r.sha(source),'receipt':str(rp),'receipt_sha256':r.sha(rp),'receipt_key_sha256':r.digest(receipt['key']),'objects':objects})
for name in ['ExtractedDecoderWithdrawalSuccess','ExtractedWithdrawalCallerPublic']:visit(name)
for x,label in [(c,'decoder_checked'),(p,'public_checked')]:data['roots'].insert(0,{'name':label,'source':str(x/'sources'),'objects':str(x/'objects')})
freeze=w/'input-manifests';freeze.mkdir(exist_ok=True)
for x,label in [(c,'decoder'),(p,'public')]:
 target=freeze/(label+'.json');r.dump(target,manifest_by_root[x]);data['provenance_files'][str(target)]=r.sha(target)
target=freeze/'base-public-snapshot.json';r.dump(target,json.loads(base.read_text()));data['provenance_files'][str(target)]=r.sha(target)
data['captured_utc']=datetime.now(timezone.utc).isoformat()
data['scope']='Read/hash only extension by exact source/runtime/import/object receipts for Decoder success and final adapted CallerPublic. No object relocation or claim that a joint import succeeds.'
r.dump(w/'external-inputs-caller.json',data);r.dump(w/'import-source-audit.json',records)
name='DecoderCallerJoint';source=w/'sources'/(name+'.lean')
item={'source':'diagnostic/'+name+'.lean','source_sha256':r.sha(source),'source_revision':'92756a3c1098e3c1c3e2586ec303fbae20191292 plus actual Decoder withdrawal inversion','imports':r.imports(source),'stage_as':name+'.lean','role':'Joint-import diagnostic only; no theorem','axiom_requests':0}
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':{name:item},'topological_order':[name],'groups':{}});r.staged(w)
print(json.dumps({'extension_count':len(records),'snapshot_sha256':r.sha(w/'external-inputs-caller.json'),'source_sha256':r.sha(source)},indent=2))
