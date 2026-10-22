"""Check final audit object/source pins; no unchanged compiler replay."""
import json,hashlib,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
code='''from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit29-20261022')
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
a=json.loads((H/'lean-7867.json').read_text())
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[J/'objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
diffs=[]
for name,want in a['deps']:
 rel=Path(name.replace('.','/')+'.olean')
 p=next((d/rel for d in paths if (d/rel).exists()),None)
 got=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 if got!=want:diffs.append(dict(module=name,want=want,got=got))
modules=['R1Z.ProverCommitFieldsSource29','R1Z.ProverCommitFields29','R1Z.ProverCommitStepSource29','R1Z.ProverCommitStep29','R1Z.ProverCommitRows29','R1Z.ProverCommitWalk29','R1Z.ProverCommit29Audit']
sources={m:hashlib.sha256((J/'sources'/Path(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in modules}
print(json.dumps(dict(audit_attempt=7867,checked_import_objects=len(a['deps']),object_differences=diffs,source_sha256=sources)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True)
x=json.loads(r.stdout);assert x['object_differences']==[],x
L=Path('docs/research/v8-r0-zk-20261009/lean')
for name,want in x['source_sha256'].items():assert hashlib.sha256((L/Path(name.replace('.','/')+'.lean')).read_bytes()).hexdigest()==want,name
x['local_sources_match']=True;x['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
(E/'closure-check.json').write_text(json.dumps(x,indent=2)+'\n');print({k:x[k] for k in ['checked_import_objects','object_differences','local_sources_match']})
