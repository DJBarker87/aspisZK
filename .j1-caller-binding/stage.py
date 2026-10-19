from pathlib import Path
from datetime import datetime, timezone
import importlib.util,json
B=Path('/home/dombarker/project-offloads')
w=B/'aspis-r1-caller-binding-20261016'
p=B/'aspis-r1-j1a-terminal-decoder-copy-helper-proof-20261016/caller-adapted'
spec=importlib.util.spec_from_file_location('runner',w/'runner.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
base=p/'external-inputs-public.json';data,_=r.verify_snapshot(base)
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
 data['modules'][name]={'root':'decoder_public_checked','source':str(source),'source_sha256':r.sha(source),'imports':deps,'objects':objects,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}}
 records.append({'module':name,'source_sha256':r.sha(source),'receipt':str(rp),'receipt_sha256':r.sha(rp),'receipt_key_sha256':r.digest(receipt['key']),'objects':objects})
visit('ExtractedDecoderPublicBridge')
data['roots'].insert(0,{'name':'decoder_public_checked','source':str(p/'sources'),'objects':str(p/'objects')})
freeze=w/'input-manifests';freeze.mkdir(exist_ok=True)
for name,value in [('decoder-public',manifest),('base-snapshot',json.loads(base.read_text()))]:
 f=freeze/(name+'.json');r.dump(f,value);data['provenance_files'][str(f)]=r.sha(f)
data['scope']='Exact source/runtime/import/object receipt extension for one fixed Decoder-to-public carrier bridge. No replay, cache relocation, or source caller refinement.'
data['captured_utc']=datetime.now(timezone.utc).isoformat()
r.dump(w/'external-inputs-binding.json',data);r.dump(w/'import-source-audit.json',records)
name='ExtractedDecoderPublicBinding';source=w/'sources'/(name+'.lean')
item={'source':'docs/research/100bit-spend-path-20261013/lean/'+name+'.lean','source_sha256':r.sha(source),'source_revision':'ca137f5db50123d6157ce144e43e4f15d8fad94b plus new owned bridge','imports':r.imports(source),'stage_as':name+'.lean','role':'Fixed full transition and variant projection; actual decoder and serializer success remain explicit','axiom_requests':7}
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':{name:item},'topological_order':[name],'groups':{}});r.staged(w)
print(json.dumps({'extension_count':len(records),'snapshot_sha256':r.sha(w/'external-inputs-binding.json'),'source_sha256':r.sha(source)},indent=2))
