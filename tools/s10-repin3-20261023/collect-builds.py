#!/usr/bin/env python3
"""Collect host-only build hashes/receipts, never binaries or wallet keys."""
import hashlib,json,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023'
H='/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023'
REMOTE='dombarker@100.108.41.90'
code='''
from pathlib import Path
import hashlib,json
H=Path(%r)
pin=lambda p:dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
source=json.loads((H/'source-inputs.json').read_text())
for r in source['files']+source['additional_workspace_inputs']:
 assert pin(H/'src'/r['path'])['sha256']==r['sha256'],r['path']
builds=[]
for d in sorted(H.glob('build-*-v*')):
 if not d.is_dir():continue
 files=[p for p in d.rglob('*') if p.is_file()]
 builds.append(dict(name=d.name,outputs=[pin(p) for p in files]))
print(json.dumps(dict(source_revision=source['source_revision'],source_files_rehashed=len(source['files'])+len(source['additional_workspace_inputs']),builds=builds)))
''' % H
import shlex
x=json.loads(subprocess.check_output(['ssh',REMOTE,'python3 -c '+shlex.quote(code)],text=True))
for b in x['builds']:
 b['actual_source_revision']=x['source_revision']
 d=E/b['name'];d.mkdir(exist_ok=True)
 for p in b['outputs']:
  s=p['path'];name=Path(s).name
  if '/receipt/' in s or name in ('command.json','reservation.json','artifact-comparison.json'):
   subprocess.run(['scp','-q',REMOTE+':'+s,str(d/name)],check=True)
   assert hashlib.sha256((d/name).read_bytes()).hexdigest()==p['sha256']
   if name=='artifact-comparison.json':b['comparison']=json.loads((d/name).read_text())
x.update(schema='s10-adopted-builds-v1',print_axioms='N/A: no Lean; compiler diagnostics only',host_workspace=H)
x['receipt_revision_correction']='The reused capped.py writes a hard-coded historical b2727acd source_revision. Raw receipts are retained byte-for-byte. Actual source for every build is source-inputs.json, revision '+x['source_revision']+'. No historical source assertion is transferred.'
(E/'build-manifest.json').write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(builds=len(x['builds']),source_files=x['source_files_rehashed'])))
