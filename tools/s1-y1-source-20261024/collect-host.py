#!/usr/bin/env python3
"""Collect source/receipts only. Never LLBC, build products or binaries."""
from pathlib import Path
import subprocess,sys,tarfile,tempfile,json
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-y1-source'
for name in sys.argv[1:]:
 assert name in ['native-v1','native-v2','native-v3','native-v4','native-v5','owned-extraction-v1','owned-extraction-v2','owned-extraction-v3']
 remote='s1-y1-'+name+'-20261024';out=E/name;out.mkdir(parents=True,exist_ok=False)
 script='''from pathlib import Path
import json,tarfile,sys,hashlib
W=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')/NAME
fingerprints=[]
for p in (W/'target').rglob('*.json'):
 if '.fingerprint' in str(p):
  try:r=json.loads(p.read_text())
  except:continue
  if 'rustflags' in r:fingerprints.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'rustflags':r['rustflags']})
if fingerprints:(W/'compilation-fingerprints.json').write_text(json.dumps(fingerprints,indent=2)+'\\n')
remaining={}
for p in W.rglob('receipt.json'):
 if 'target' in p.parts:continue
 r=json.loads(p.read_text());cg=Path(r.get('cgroup','/nonexistent'))
 remaining[str(p.relative_to(W))]=(cg/'cgroup.procs').read_text().split() if (cg/'cgroup.procs').exists() else []
assert all(not pids for pids in remaining.values()),remaining
(W/'terminal-process-review.json').write_text(json.dumps(remaining,indent=2)+'\\n')
files=[p for p in W.rglob('*') if p.is_file() and 'target' not in p.parts and (p.suffix in ['.json','.log','.rs','.toml','.lean'] or p.name=='Cargo.lock')]
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|') as t:
 for p in files:t.add(p,arcname=str(p.relative_to(W)),recursive=False)
'''.replace('NAME',repr(remote))
 with tempfile.NamedTemporaryFile(suffix='.tar') as f:
  subprocess.run(['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3','-'],input=script.encode(),stdout=f,check=True)
  f.flush()
  with tarfile.open(f.name) as t:
   for m in t.getmembers():assert m.isfile() and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts
   t.extractall(out,filter='data')
 for p in out.rglob('*.lean'):p.rename(p.with_name(p.name+'.txt'))
 print('Collected source-only',name)
