"""Read-only identity inventory for current focused compiled dependency closure."""
from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
E=H/'rng-material'
rows={}
for p in sorted(E.glob('*-receipt.json')):
 r=json.loads(p.read_text())
 if r['exit_status']==0:rows[r['module']]=r
paths=set()
for r in rows.values():
 paths.add(str(J/'objects'/(r['module']+'.olean')))
 paths.add(r['source_path'])
 for d in r['dependencies']:
  paths.add(d['resolved_object'])
  source=J/'sources'/(d['module'].replace('.','/')+'.lean')
  if source.is_file():paths.add(str(source))
files=[]
for name in sorted(paths):
 p=Path(name);files.append(dict(path=name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(E/'current-closure-hashes.json').write_text(json.dumps(dict(schema='rng-material-focused-closure-identity-v1',print_axioms='N/A: read-only hash inventory',files=files),indent=2)+'\n')
print('Hashed',len(files),'current source/object files; no build')
