"""Fresh resume ledger wrapper for the standing one-module Env-J runner."""
from pathlib import Path
import json,sys,subprocess,shlex,time
root=Path(__file__).resolve().parents[2]
out=root/'evidence/pv-cblib-20261027';p=out/'TALLY.json'
module=sys.argv[1];assert module.startswith('R1Z/PV_CBL_')
r=json.loads(p.read_text());assert len(r['lean_charged'])<100
if len(r['lean_charged'])>=97:assert 'Audit' in module or 'Manifest' in module
attempt=(41797+len(r['lean_charged'])-97 if len(r['lean_charged'])>=97 else r['next_id']);assert 41588<=attempt<=41799 and attempt not in r['used_ids']
r['used_ids'].append(attempt);r['next_id']=attempt+1;p.write_text(json.dumps(r,indent=2)+'\n')
source=root/'docs/research/v8-r0-zk-20261009/lean'/f'{module}.lean';assert source.exists()
(out/f'{attempt}-source.lean.txt').write_text(source.read_text())
host='dombarker@100.108.41.90';base='/home/dombarker/project-offloads/codex-pv-cblib-20261027';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
def ssh(c):return subprocess.run(['ssh',host,c],text=True,capture_output=True)
a=ssh(f'python3 {gate}/reservation.py {base}/resume8-{attempt}-admission.json > {base}/resume8-{attempt}-reservation.log 2>&1; cat {base}/resume8-{attempt}-reservation.log')
(out/f'{attempt}-upload-admission.log').write_text(a.stdout+a.stderr)
if a.returncode or not json.loads(a.stdout)['allowed']:
 (out/f'{attempt}-refusal.json').write_text(json.dumps(dict(attempt=attempt,charged=False,phase='before upload',output=a.stdout+a.stderr),indent=2)+'\n');sys.exit(78)
# Snapshot previously published shared source and object before own-prefix update.
shared='/home/dombarker/project-offloads/aspis-joint-20261019'
b=ssh(f'mkdir -p {base}/resume8-snapshots/{attempt}; for f in {shared}/sources/{module}.lean {shared}/objects/{module}.olean; do if test -f "$f"; then cp "$f" {base}/resume8-snapshots/{attempt}/; fi; done')
assert b.returncode==0,b.stderr
subprocess.run(['scp',str(source),f'{host}:{shared}/sources/{module}.lean'],check=True)
c=subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/resume_lean.py'),str(attempt),module])
r=json.loads(p.read_text())
if (out/f'{attempt}.json').exists():
 r['lean_charged'].append(attempt)
 q=out/f'{attempt}.json';v=json.loads(q.read_text());v['limits']['TasksMax']=64;v['source_snapshot']=f'{attempt}-source.lean.txt';q.write_text(json.dumps(v,indent=2)+'\n')
p.write_text(json.dumps(r,indent=2)+'\n');sys.exit(c.returncode)
