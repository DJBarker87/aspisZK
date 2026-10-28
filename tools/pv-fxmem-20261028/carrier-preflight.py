"""Read-only h4/h5 source and object verification for the original carrier."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
base=R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'
project={}
for name in ['ProverRwFullExternalTypes','ProverRwFullTypes','ProverRwFullExternalFuns']:
 p=base/(name+'.lean');rel=str(p.relative_to(R));blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],text=True).strip()
 project['R1Z/'+name]=dict(path=rel,blob=blob,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),resolution='h5: tracked candidate module at HEAD; absent EJR')
ejr=json.loads(subprocess.check_output(['git','show','research:evidence/envj-rebuild-20261026/EJR_final-inventory.json']))
for x in ejr['selected']:
 assert x['module'].replace('.','/') not in project, ('EJR precedence requires resolution',x)
manifest=json.loads((E/'external-object-manifest.json').read_text())
code='''from pathlib import Path
import hashlib,json
b=Path('/home/dombarker/project-offloads');e=json.loads((b/'r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[b/'aspis-joint-20261019/objects']+[Path(x) for x in e['LEAN_PATH'].split(':')]
external=[]
for x in MANIFEST:
 p=next((r/(x['module']+'.olean') for r in roots if (r/(x['module']+'.olean')).exists()),None)
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 external.append(dict(module=x['module'],path=str(p),sha256=h,expected=x['object_sha256'],ok=h==x['object_sha256']))
project=PROJECT
for m,x in project.items():
 p=b/'aspis-joint-20261019/sources'/(m+'.lean');o=next((r/(m+'.olean') for r in roots if (r/(m+'.olean')).exists()),None)
 x.update(host_source=str(p),host_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),object=str(o),object_sha256=hashlib.sha256(o.read_bytes()).hexdigest() if o else None)
 x['ok']=x['host_source_sha256']==x['sha256'] and o is not None
print(json.dumps(dict(env=e,external=external,project=project)))
'''.replace('MANIFEST',repr(manifest)).replace('PROJECT',repr(project))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
if r.returncode: print(r.stderr);raise SystemExit(r.returncode)
j=json.loads(r.stdout);j['revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();j['ok']=all(x['ok'] for x in j['external']) and all(x['ok'] for x in j['project'].values())
(E/'CARRIER-PREFLIGHT.json').write_text(json.dumps(j,indent=2)+'\n'); print(json.dumps(dict(ok=j['ok'],external_count=len(j['external']),bad=[x for x in j['external'] if not x['ok']],project=j['project'])))
