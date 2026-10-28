"""Recover terminal receipt source snapshots read-only; never submit a job."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
attempts=[json.loads(l)['attempt'] for l in (E/'NDD_ATTEMPTS.jsonl').read_text().splitlines()]
code='''from pathlib import Path
import json
b=Path('/home/dombarker/project-offloads/codex-cx-native-front1-20261028');out={}
for a in ATTEMPTS:
 p=b/a/'sources'
 assert (b/a/'receipt.json').is_file(),a
 for f in p.rglob('*'):
  if f.is_file():
   assert f.suffix not in ['.olean','.rlib','.so','.pyc'],str(f)
   out[str(f.relative_to(b))]=f.read_text()
print(json.dumps(out))
'''.replace('ATTEMPTS',repr(attempts))
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 if r.returncode!=255:break
 if retry==10:raise SystemExit('read-only transport exhausted; no resubmission')
 time.sleep(60)
assert r.returncode==0,r.stderr
files=json.loads(r.stdout)
for n,s in files.items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_text()==s,('source snapshot mismatch',n)
 else:p.write_text(s)
print(json.dumps(dict(source_snapshots=len(files),attempts=len(attempts),read_only=True)))
