"""Stage a frozen set of own modules; collect each unchanged launcher receipt."""
from pathlib import Path
import subprocess,json,sys,datetime,time,shlex,hashlib
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cb3-20261026'
name=sys.argv[1];modules=sys.argv[2:];assert modules and all(m.startswith('R1Z/PV_CB3_') for m in modules)
state=out/'RESUME6_ADMISSION_STATE.json'
if state.exists():
    d=json.loads(state.read_text());left=datetime.datetime.fromisoformat(d['utc']).timestamp()+180-time.time()
    if not d.get('allowed',False) and left>0:print('LOCAL COOLDOWN',left);sys.exit(78)
local=out/name;local.mkdir(exist_ok=True);assert not (local/'manifest.json').exists()
host='dombarker@100.108.41.90';base='/home/dombarker/project-offloads/codex-pv-cb3-20261026'
remote=base+'/'+name;shared='/home/dombarker/project-offloads/aspis-joint-20261019'
scanner='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
def ssh(c):return subprocess.run(['ssh',host,c],capture_output=True,text=True)
a=ssh(f'mkdir -p {remote}/snapshots; python3 {scanner} {remote}/upload-admission.json')
(local/'upload-admission.log').write_text(a.stdout+a.stderr)
d=json.loads(a.stdout)
if not d['allowed']:
    state.write_text(json.dumps(dict(d,origin=name+' upload'))+'\n');sys.exit(78)
ledger=out/'RESUME6_TALLY.json';r=json.loads(ledger.read_text());assert len(r['lean_charged'])+len(modules)<=97
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();spec=[]
for module in modules:
    attempt=r['next_id'];assert 38700<=attempt<=38999 and attempt not in r['used_ids']
    r['next_id']+=1;r['used_ids'].append(attempt)
    p=root/'docs/research/v8-r0-zk-20261009/lean'/(module+'.lean')
    spec.append(dict(attempt=attempt,module=module,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),revision=rev))
    (out/f'{attempt}-source.lean.txt').write_text(p.read_text())
r['lean_inflight']=[x['attempt'] for x in spec];ledger.write_text(json.dumps(r,indent=2)+'\n')
(local/'manifest.json').write_text(json.dumps(spec,indent=2)+'\n')
# Own-prefix source/object snapshots before this job's source updates.
for row in spec:
    module=row['module'];attempt=row['attempt']
    assert ssh(f'mkdir -p {remote}/snapshots/{attempt}; for f in {shared}/sources/{module}.lean {shared}/objects/{module}.olean; do if test -f "$f"; then cp "$f" {remote}/snapshots/{attempt}/; fi; done').returncode==0
sources=[str(root/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')) for m in modules]
subprocess.run(['scp',*sources,f'{host}:{shared}/sources/R1Z/'],check=True)
subprocess.run(['scp',str(local/'manifest.json'),str(root/'tools/pv-cb3-20261026/resume6_batch_host.py'),f'{host}:{remote}/'],check=True)
run=subprocess.run(['ssh',host,'python3 '+remote+'/resume6_batch_host.py '+remote+'/manifest.json'],text=True,capture_output=True)
(local/'transport.log').write_text(run.stdout+run.stderr);print(run.stdout+run.stderr,flush=True)
r=json.loads(ledger.read_text())
for row in spec:
    attempt=row['attempt'];module=row['module']
    result=ssh(f'cat {remote}/{attempt}-launch.log 2>/dev/null');log=result.stdout
    (out/f'launch-{attempt}-resume.log').write_text(log)
    before=ssh(f'cat {remote}/{attempt}-preflight.json 2>/dev/null')
    if before.returncode==0:(out/f'{attempt}-preflight.json').write_text(before.stdout)
    timed=ssh(f'test -f /home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/time-{attempt}.log')
    if 'exit=' in log and timed.returncode==0:
        subprocess.run([sys.executable,str(root/'tools/pv-cb3-20261026/resume_receipt.py'),str(attempt),module],check=True)
        r['lean_charged'].append(attempt)
    else:
        a=ssh(f'cat {remote}/{attempt}-admission.json 2>/dev/null')
        refusal=dict(attempt=attempt,charged=False,phase='batch admission' if a.returncode==0 else 'retired unlaunched batch suffix',output=a.stdout or log,module=module)
        (out/f'{attempt}-refusal.json').write_text(json.dumps(refusal,indent=2)+'\n')
        if a.returncode==0:
            d=json.loads(a.stdout)
            if not d.get('allowed',False):state.write_text(json.dumps(dict(d,origin=f'Env-J {attempt} batch'))+'\n')
        if a.returncode==0 or log:r.setdefault('reservation_refusals',[]).append(attempt)
        else:r.setdefault('retired_unlaunched',[]).append(attempt)
r['lean_inflight']=[];ledger.write_text(json.dumps(r,indent=2)+'\n')
sys.exit(run.returncode)
