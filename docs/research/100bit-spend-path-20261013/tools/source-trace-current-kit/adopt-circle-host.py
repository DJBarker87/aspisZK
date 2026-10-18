from pathlib import Path
import json,importlib.util
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-source-trace-proof-20261018');A=Path('/home/dombarker/project-offloads/aspis-r1-worker-a-rounds-proof-20261017')
sp=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(sp);sp.loader.exec_module(r)
D=json.loads((W/'external-inputs.json').read_text());n='ExtractedCircleCalls';rp=A/'runs/circle-calls-b/receipt.json';ip=rp.parent/'input-manifest.json';rc=json.loads(rp.read_text());im=json.loads(ip.read_text());assert r.sha(ip)==rc['input_manifest_sha256'];checked=[]
for dep,v in im['current_finish_import_closure'].items():
 cur=D['modules'][dep];assert cur['source_sha256']==v['source_sha256'],dep
 assert {s:o['sha256'] for s,o in cur['objects'].items()}=={s:o['sha256'] for s,o in v['objects'].items()},dep
 assert r.imports(v['source'],True)==cur['imports'],dep
 checked.append(dep)
# Direct third source dependency retained in the canonical producing pins.
for dep in ['ExtractedDigest32Callers']:
 v=im['current_canonical_and_begin_pins'].get(dep)
 if v is None:v=im['current_opening_pins'].get(dep)
 assert v is not None,dep
 assert D['modules'][dep]['source_sha256']==v['source_sha256'],dep
 assert D['modules'][dep]['objects']['.olean']['sha256']==v['object_sha256'],dep
 checked.append(dep)
src=A/'sources'/(n+'.lean');ob=r.object_pins(A/'objects',n,D['olean_header_seal']);assert rc['exit_status']==0 and rc['source_sha256']==r.sha(src) and rc['olean_sha256']==ob['.olean']['sha256'];assert r.audits(src,(rp.parent/'lean.log').read_text())['passed']
for p,h in rc['runtime_sha256'].items():assert D['runtime_files'][p]==h,p
root='current_a_circle';D['roots'].append({'name':root,'source':str(A/'sources'),'objects':str(A/'objects')});D['modules'][n]={'root':root,'source':str(src),'source_sha256':r.sha(src),'imports':r.imports(src,True),'objects':ob,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}}
D['provenance_files'][str(rp)]=r.sha(rp);D['provenance_files'][str(ip)]=r.sha(ip)
r.dump(W/'circle-leaf-current-adoption-audit.json',{'module':n,'producing_manifest':str(ip),'producing_manifest_sha256':r.sha(ip),'checked_imports':checked,'scope':'Exact current source/object/header/runtime producing identity; no Lean replay.'})
(W/'external-inputs-before-circle.json').write_bytes((W/'external-inputs.json').read_bytes());r.dump(W/'external-inputs.json',D);print('ADOPTED',n,len(checked))
