from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_ReserveErrorSource.lean'
m='R1Z/PDict_ReserveErrorSource';j=json.loads((E/'CARRIER-FUNS-PREFLIGHT.json').read_text());assert j['ok']
x=dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),resolution='h5: tracked candidate source; no EJR entry')
ejr=json.loads(subprocess.check_output(['git','show','research:evidence/envj-rebuild-20261026/EJR_final-inventory.json']))
assert not any(q['module'].replace('.','/')==m for q in ejr['selected'])
code='''from pathlib import Path
import json,hashlib
b=Path('/home/dombarker/project-offloads');e=json.loads((b/'r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[b/'aspis-joint-20261019/objects']+[Path(p) for p in e['LEAN_PATH'].split(':')]
m='R1Z/PDict_ReserveErrorSource';s=b/'aspis-joint-20261019/sources'/(m+'.lean');p=next(r/(m+'.olean') for r in roots if (r/(m+'.olean')).exists())
print(json.dumps(dict(env=e,host_source=str(s),host_source_sha256=hashlib.sha256(s.read_bytes()).hexdigest(),object=str(p),object_sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
a=json.loads(r.stdout);assert a.pop('env')==j['env'];x.update(a);assert x['sha256']==x['host_source_sha256'];x['ok']=True
j['project'][m]=x;j['extension']='ReserveErrorSource imports only Aeneas, already fully h4-verified.'
(E/'CARRIER-RESERVE-PREFLIGHT.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS selected reserve error source/object carrier')
