from pathlib import Path
import json,hashlib,subprocess,shlex
E=Path(__file__).resolve().parent.parent
x=json.loads((E/'lean/lean-7871.json').read_text())
imports=dict(x['deps'])
root=Path('docs/research/v8-r0-zk-20261009/lean')
modules={m:hashlib.sha256((root/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in imports if (root/(m.replace('.','/')+'.lean')).exists()}
modules['R1Z.ProverCommit30Audit']=hashlib.sha256((root/'R1Z/ProverCommit30Audit.lean').read_bytes()).hexdigest()
code='''from pathlib import Path
import json,hashlib
x=json.loads(input());J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[J/'objects']+[Path(p) for p in env['LEAN_PATH'].split(':')]
def obj(m):
 r=Path(m.replace('.','/')+'.olean');return next((d/r for d in paths if (d/r).exists()),J/'objects'/r)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
print(json.dumps(dict(objects={m:sha(obj(m)) for m in x['objects']},sources={m:sha(J/'sources'/Path(m.replace('.','/')+'.lean')) for m in x['sources']})))
'''
actual=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(objects=imports,sources=modules)),text=True))
errors=[m for m,h in imports.items() if actual['objects'][m]!=h]+[m for m,h in modules.items() if actual['sources'][m]!=h]
assert not errors,errors
(E/'closure-check.json').write_text(json.dumps(dict(audit_attempt=7871,checked_objects=len(imports),checked_sources=len(modules),errors=errors,sources=modules,objects=imports),indent=2)+'\n')
print(len(imports),'object pins,',len(modules),'source pins; no differences')
