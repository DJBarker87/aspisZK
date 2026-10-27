"""Admission-checked upload of own cfg(kani) proof inputs only."""
from pathlib import Path
import json,subprocess,sys,time,datetime
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cb3-20261026';name=sys.argv[1]
# Own-job cooldown only; shared admission infrastructure is unchanged.
state=out/'RESUME6_ADMISSION_STATE.json'
if state.exists():
 d=json.loads(state.read_text())
 when=datetime.datetime.fromisoformat(d['utc']).timestamp()
 left=when+180-time.time()
 if not d.get('allowed',False) and left>0:
  print(f'LOCAL COOLDOWN HOLD {left:.1f}s; no ID or compiler charged');sys.exit(78)

for old in sorted(out.glob('38*-refusal.json'),reverse=True):
 try:d=json.loads(json.loads(old.read_text()).get('output',''));when=datetime.datetime.fromisoformat(d['utc']).timestamp()
 except (ValueError,KeyError,TypeError):continue
 left=when+180-time.time()
 if left>0:print('LOCAL COOLDOWN HOLD',left);sys.exit(78)
 break
host='dombarker@100.108.41.90';base='/home/dombarker/project-offloads/codex-pv-cb3-20261026';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
p=out/(name+'.json');assert not p.exists()
r=subprocess.run(['ssh',host,f'python3 {gate}/reservation.py {base}/{name}.json > {base}/{name}.log 2>&1; cat {base}/{name}.log'],text=True,capture_output=True)
(out/(name+'.log')).write_text(r.stdout+r.stderr)
d=json.loads(r.stdout);p.write_text(json.dumps(d,indent=2)+'\n')
if not d['allowed']:
 (out/'RESUME6_ADMISSION_STATE.json').write_text(json.dumps(dict(d,origin=name))+'\n')
 print('REFUSED',d['utc']);sys.exit(78)
mapping={'kani-lib.rs':'kani-proof/lib.rs','resume6_mask_reference.rs':'kani-proof/resume6_mask_reference.rs',
 'source-lib.rs':'source-proof/lib.rs','resume6_weights.rs':'source-proof/resume6_weights.rs'}
files=sys.argv[2:] or ['kani-lib.rs','resume6_mask_reference.rs']
assert set(files)<=set(mapping)
for file in files:
 subprocess.run(['scp',str(root/'tools/pv-cb3-20261026'/file),f'{host}:{base}/{mapping[file]}'],check=True)
print('Uploaded own cfg(kani) mask inputs after admission',d['utc'])
