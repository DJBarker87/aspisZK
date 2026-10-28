"""One no-stub control-only native gate; a single capped scope, optimized MIR."""
from pathlib import Path
import json,datetime,subprocess,shlex,time,re,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028';H='/home/dombarker/project-offloads/codex-pv-l2c-20261028';host='dombarker@100.108.41.90'
old=[json.loads(p.read_text()) for p in E.glob('refusal-*.json')]
if old:
 last=max(datetime.datetime.fromisoformat(x['utc']) for x in old)
 remaining=180-(datetime.datetime.now(datetime.timezone.utc)-last).total_seconds()
 if remaining>0:print('WAIT',remaining,'seconds; no native differential launched');sys.exit(77)
n=1
while (E/f'differential-{n}').exists():n+=1
d=E/f'differential-{n}';d.mkdir()
def ssh(cmd):return subprocess.run(['ssh',host,cmd],capture_output=True,text=True)
res=f'{H}/evidence/differential-{n}-reservation'
p=ssh(f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {res}.json > {res}.log 2>&1\ns=$?\ncat {res}.log\nexit $s')
(d/'reservation.log').write_text(p.stdout+p.stderr);gate=json.loads(p.stdout.strip().splitlines()[-1]);(d/'reservation.json').write_text(json.dumps(gate,indent=2)+'\n')
if p.returncode!=0 or not gate['allowed']:
 (E/f'refusal-differential-{n}.json').write_text(json.dumps(gate,indent=2)+'\n');print('REFUSED',gate);sys.exit(78)
assert subprocess.run(['python3',str(R/'tools/pv-l2c-20261028/generate-balance-cut.py'),'--check']).returncode==0
assert ssh(f'mkdir -p {H}/differential').returncode==0
subprocess.run(['scp','-q',str(R/'tools/pv-l2c-20261028/native-receipt.py'),f'{host}:{H}/native-receipt.py'],check=True)
for f in ['Cargo.toml','main.rs','balance_cut.rs']:
 subprocess.run(['scp','-q',str(R/'tools/pv-l2c-20261028/differential'/f),f'{host}:{H}/differential/{f}'],check=True)
p=subprocess.run(['python3',str(R/'tools/pv-l2c-20261028/native-preflight.py')],capture_output=True,text=True);(d/'source-preflight.log').write_text(p.stdout+p.stderr);assert p.returncode==0,p.stdout+p.stderr
# Seed only this job's lockfile with the frozen registry versions. Cargo may
# update its own package section; no dependency source/other workspace is written.
assert ssh(f'cp /home/dombarker/project-offloads/codex-pv-integ4-20261027/source/Cargo.lock {H}/differential/Cargo.lock').returncode==0
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=l2c-differential-{n}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PV8_SOURCE_DIR='+H+'/differential','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+H+'/differential-target','CARGO_BUILD_JOBS=4','CARGO_NET_OFFLINE=true','PV_L2C_PIN_FILES=Cargo.toml:Cargo.lock:main.rs:balance_cut.rs','PV_L2C_EXPECTED_TIME=Optimized compilation then 128 named balancing native differential cases','PV_L2C_EVIDENCE_CLASS=N/A: finite native validation, not universal proof','python3',H+'/native-receipt.py',H+f'/evidence/differential-{n}-native','timeout','180','taskset','--cpu-list','0-3','cargo','run','--release','--offline','-j','4']
record=dict(target='balance same-input differential',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=cmd,source_sha256={f:hashlib.sha256((R/'tools/pv-l2c-20261028/differential'/f).read_bytes()).hexdigest() for f in ['Cargo.toml','main.rs','balance_cut.rs']},scope='Finite native differential, 14 verbatim shipped/reference declarations and native aspis-core fields; no universal source equivalence claimed',expected_time='optimized compilation, then 128 full-output table comparisons',print_axioms='N/A: finite native Rust validation',caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(d/'invocation.json').write_text(json.dumps(record,indent=2)+'\n');start=time.monotonic();print('LAUNCH DIFFERENTIAL',n,flush=True)
p=ssh(f'cd {H}/differential && '+shlex.join(cmd)+f' > {H}/evidence/differential-{n}.log 2>&1');record['exit']=p.returncode;record['wall_seconds']=time.monotonic()-start
q=ssh(f'cat {H}/evidence/differential-{n}-native/receipt.json');assert q.returncode==0,q.stderr
aggregate=json.loads(q.stdout);(d/'aggregate-receipt.json').write_text(q.stdout)
record.update({k:aggregate[k] for k in ['peak_rss_bytes','cgroup_peak_bytes','swaps','scope_swap_peak_bytes','controls','cgroup','removed_owned_solver_temps']})
q=ssh(f'cat {H}/evidence/differential-{n}-native/out.log');assert q.returncode==0,q.stderr;out=q.stdout;(d/'out.log').write_text(out)
record['finite_validation_successful']='FINITE VALIDATION: 128' in out
(d/'receipt.json').write_text(json.dumps(record,indent=2)+'\n');print(out[-7000:]);print('RECEIPT',json.dumps(record),flush=True)
sys.exit(p.returncode)
