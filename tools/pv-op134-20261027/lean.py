"""Allocate IDs durably, admit before upload, compile only own new modules."""
from pathlib import Path
import subprocess,json,sys,shlex,time
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-op134-20261027'
base='/home/dombarker/project-offloads/codex-pv-op134-20261027';host='dombarker@100.108.41.90'
gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
module=sys.argv[1];assert module.startswith('R1Z/PV_Op134_')
p=out/'TALLY.json';r=json.loads(p.read_text());assert len(r['lean_charged'])<100
if len(r['lean_charged'])>=97:assert 'Audit' in module or 'Manifest' in module or 'Bundle' in module
state=out/'admission-state.json'
if state.exists():
 s=json.loads(state.read_text());left=s['retry_after']-time.time()
 if left>0:print('COOLDOWN',left);sys.exit(78)
a=r['next_id']
if len(r['lean_charged']) >= 97:
 a=next((i for i in r['reserved_audit_ids'] if i not in r['used_ids']),
        next(i for i in range(50000,50297) if i not in r['used_ids']))
if a>=50297:assert any(x in module for x in ['Audit','Manifest','Bundle'])
assert 50000<=a<=50299 and a not in r['used_ids']
r['used_ids'].append(a);r['next_id']=a+1;p.write_text(json.dumps(r,indent=2)+'\n')
src=root/'docs/research/v8-r0-zk-20261009/lean'/f'{module}.lean';assert src.exists()
(out/f'{a}-source.lean.txt').write_text(src.read_text())
def ssh(s):return subprocess.run(['ssh',host,s],capture_output=True,text=True)
quiet="import pathlib,json,time; p=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json'); until=float(json.loads(p.read_text()).get('until',0)) if p.exists() else 0; held=time.time()<until; print(json.dumps(dict(allowed=False,reason='QUIET WINDOW HOLD',until=until))) if held else None; raise SystemExit(78 if held else 0)"
x=ssh(f'python3 -c {shlex.quote(quiet)} > {base}/lean-{a}-reservation.log 2>&1 && python3 {gate}/reservation.py {base}/lean-{a}-admission.json >> {base}/lean-{a}-reservation.log 2>&1; status=$?; cat {base}/lean-{a}-reservation.log; exit $status')
(out/f'{a}-admission.log').write_text(x.stdout+x.stderr)
if x.returncode:
 (out/f'{a}-refusal.json').write_text(json.dumps(dict(charged=False,exit=x.returncode,reason=x.stdout+x.stderr),indent=2)+'\n')
 state.write_text(json.dumps(dict(retry_after=time.time()+(30 if 'FileNotFoundError' in x.stdout else 180),reason=x.stdout+x.stderr))+'\n');sys.exit(78)
shared=base
assert ssh(f'mkdir -p {base}/snapshots/{a} {shared}/sources/R1Z; for f in {shared}/sources/{module}.lean {shared}/objects/{module}.olean; do if test -f "$f"; then cp "$f" {base}/snapshots/{a}/; fi; done').returncode==0
subprocess.run(['scp',str(src),f'{host}:{shared}/sources/{module}.lean'],check=True)
x=subprocess.run([sys.executable,str(root/'tools/pv-op134-20261027/launch.py'),str(a),module])
r=json.loads(p.read_text())
if (out/f'{a}.json').exists():r['lean_charged'].append(a)
p.write_text(json.dumps(r,indent=2)+'\n');sys.exit(x.returncode)
