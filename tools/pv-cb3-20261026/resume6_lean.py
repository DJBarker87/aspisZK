"""Fresh resume ledger wrapper for the standing one-module Env-J runner."""
from pathlib import Path
import json,sys,subprocess,shlex,time,datetime
root=Path(__file__).resolve().parents[2]
out=root/'evidence/pv-cb3-20261026';p=out/'RESUME6_TALLY.json'
module=sys.argv[1];assert module.startswith('R1Z/PV_CB3_')
# Own-job cooldown only; shared admission infrastructure is unchanged.
state=out/'RESUME6_ADMISSION_STATE.json'
if state.exists():
 d=json.loads(state.read_text())
 when=datetime.datetime.fromisoformat(d['utc']).timestamp()
 left=when+180-time.time()
 if not d.get('allowed',False) and left>0:
  print(f'LOCAL COOLDOWN HOLD {left:.1f}s; no ID or compiler charged');sys.exit(78)

# Respect the three-minute cooldown without a blocking sleep or ID reuse.
for old in sorted(out.glob('38*-refusal.json'),reverse=True):
 record=json.loads(old.read_text())
 raw=record.get('output','')
 try:
  admission=json.loads(raw)
  when=datetime.datetime.fromisoformat(admission['utc']).timestamp()
 except (ValueError,KeyError,TypeError):continue
 remaining=when+180-time.time()
 if remaining>0:
  print(f'LOCAL COOLDOWN HOLD {remaining:.1f}s; no ID or compiler charged')
  sys.exit(78)
 break
r=json.loads(p.read_text());assert len(r['lean_charged'])<100
if len(r['lean_charged'])>=97:assert 'Audit' in module or 'Manifest' in module
attempt=r['next_id'];assert 38700<=attempt<=38999 and attempt not in r['used_ids']
r['used_ids'].append(attempt);r['next_id']=attempt+1;p.write_text(json.dumps(r,indent=2)+'\n')
source=root/'docs/research/v8-r0-zk-20261009/lean'/f'{module}.lean';assert source.exists()
(out/f'{attempt}-source.lean.txt').write_text(source.read_text())
host='dombarker@100.108.41.90';base='/home/dombarker/project-offloads/codex-pv-cb3-20261026';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
def ssh(c):return subprocess.run(['ssh',host,c],text=True,capture_output=True)
a=ssh(f'python3 {gate}/reservation.py {base}/resume6-{attempt}-admission.json > {base}/resume6-{attempt}-reservation.log 2>&1; cat {base}/resume6-{attempt}-reservation.log')
(out/f'{attempt}-upload-admission.log').write_text(a.stdout+a.stderr)
if a.returncode or not json.loads(a.stdout)['allowed']:
 (out/'RESUME6_ADMISSION_STATE.json').write_text(json.dumps(dict(json.loads(a.stdout),origin=f'Env-J {attempt} upload'))+'\n')
 (out/f'{attempt}-refusal.json').write_text(json.dumps(dict(attempt=attempt,charged=False,phase='before upload',output=a.stdout+a.stderr),indent=2)+'\n');sys.exit(78)
# Snapshot previously published shared source and object before own-prefix update.
shared='/home/dombarker/project-offloads/aspis-joint-20261019'
b=ssh(f'mkdir -p {base}/resume6-snapshots/{attempt}; for f in {shared}/sources/{module}.lean {shared}/objects/{module}.olean; do if test -f "$f"; then cp "$f" {base}/resume6-snapshots/{attempt}/; fi; done')
assert b.returncode==0,b.stderr
subprocess.run(['scp',str(source),f'{host}:{shared}/sources/{module}.lean'],check=True)
c=subprocess.run([sys.executable,str(root/'tools/pv-cb3-20261026/resume_lean.py'),str(attempt),module])
r=json.loads(p.read_text())
if (out/f'{attempt}.json').exists():
 r['lean_charged'].append(attempt)
 q=out/f'{attempt}.json';v=json.loads(q.read_text());v['limits']['TasksMax']=128;v['source_snapshot']=f'{attempt}-source.lean.txt';q.write_text(json.dumps(v,indent=2)+'\n')
p.write_text(json.dumps(r,indent=2)+'\n');sys.exit(c.returncode)
