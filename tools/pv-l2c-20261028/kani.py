"""One no-stub control-only native gate; a single capped scope, optimized MIR."""
from pathlib import Path
import json,datetime,subprocess,shlex,time,re,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028';H='/home/dombarker/project-offloads/codex-pv-l2c-20261028';host='dombarker@100.108.41.90'
harness=sys.argv[1] if len(sys.argv)>1 else 'native_active_rows_match_masks'
assert harness in ['native_active_rows_match_masks','packed_masks_match_schedule','native_qm31_parser_roundtrip','packed_lane_insert']
old=[json.loads(p.read_text()) for p in E.glob('refusal-*.json')]
if old:
 last=max(datetime.datetime.fromisoformat(x['utc']) for x in old)
 remaining=180-(datetime.datetime.now(datetime.timezone.utc)-last).total_seconds()
 if remaining>0:print('WAIT',remaining,'seconds; no Kani run charged');sys.exit(77)
assert len(list(E.glob('kani-*/invocation.json')))<6
n=1
while (E/f'kani-{n}').exists():n+=1
d=E/f'kani-{n}';d.mkdir()
def ssh(cmd):return subprocess.run(['ssh',host,cmd],capture_output=True,text=True)
res=f'{H}/evidence/kani-{n}-reservation'
p=ssh(f'python3 /home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py {res}.json > {res}.log 2>&1\ns=$?\ncat {res}.log\nexit $s')
(d/'reservation.log').write_text(p.stdout+p.stderr);gate=json.loads(p.stdout.strip().splitlines()[-1]);(d/'reservation.json').write_text(json.dumps(gate,indent=2)+'\n')
if p.returncode!=0 or not gate['allowed']:
 (E/f'refusal-kani-{n}.json').write_text(json.dumps(gate,indent=2)+'\n');print('REFUSED',gate);sys.exit(78)
assert subprocess.run(['python3',str(R/'tools/pv-l2c-20261028/generate-control-cut.py'),'--check']).returncode==0
assert ssh(f'mkdir -p {H}/kani').returncode==0
subprocess.run(['scp','-q',str(R/'tools/pv-l2c-20261028/native-receipt.py'),f'{host}:{H}/native-receipt.py'],check=True)
for f in ['Cargo.toml','lib.rs','host_forest.rs','control_cut.rs']:
 subprocess.run(['scp','-q',str(R/'tools/pv-l2c-20261028/kani'/f),f'{host}:{H}/kani/{f}'],check=True)
p=subprocess.run(['python3',str(R/'tools/pv-l2c-20261028/native-preflight.py')],capture_output=True,text=True);(d/'source-preflight.log').write_text(p.stdout+p.stderr);assert p.returncode==0,p.stdout+p.stderr
# Seed only this job's lockfile with the frozen registry versions. Cargo may
# update its own package section; no dependency source/other workspace is written.
assert ssh(f'cp /home/dombarker/project-offloads/codex-pv-integ4-20261027/source/Cargo.lock {H}/kani/Cargo.lock').returncode==0
cmd=['systemd-run','--user','--scope','--quiet',f'--unit=l2c-kani-{n}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PV8_SOURCE_DIR='+H+'/kani','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+H+'/kani-target','CARGO_BUILD_JOBS=4','CARGO_NET_OFFLINE=true','CARGO_PROFILE_DEV_OPT_LEVEL=3','RUSTFLAGS=-C opt-level=3 -Z mir-opt-level=4 -Z inline-mir=yes','python3',H+'/native-receipt.py',H+f'/evidence/kani-{n}-native','timeout','180','taskset','--cpu-list','0-3','cargo','kani','-Z','unstable-options','--lib','-j','4','--exact','--harness',harness,'--output-format','terse','--cbmc-args','--unwinding-assertions','--slice-formula']
record=dict(target=harness,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=cmd,source_sha256={f:hashlib.sha256((R/'tools/pv-l2c-20261028/kani'/f).read_bytes()).hexdigest() for f in ['Cargo.toml','lib.rs','host_forest.rs','control_cut.rs']},scope='Verbatim native reachable control cut, native types and constants; generator --check pins every declaration; no field arithmetic and no stubs',expected_time='optimized compilation, then '+harness+' finite control verification',print_axioms='N/A: Kani control-only source-helper gate',caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
(d/'invocation.json').write_text(json.dumps(record,indent=2)+'\n');start=time.monotonic();print('LAUNCH KANI',n,flush=True)
p=ssh(f'cd {H}/kani && '+shlex.join(cmd)+f' > {H}/evidence/kani-{n}.log 2>&1');record['exit']=p.returncode;record['wall_seconds']=time.monotonic()-start
q=ssh(f'cat {H}/evidence/kani-{n}-native/receipt.json');assert q.returncode==0,q.stderr
aggregate=json.loads(q.stdout);(d/'aggregate-receipt.json').write_text(q.stdout)
record.update({k:aggregate[k] for k in ['peak_rss_bytes','cgroup_peak_bytes','swaps','scope_swap_peak_bytes','controls','cgroup','removed_owned_solver_temps']})
q=ssh(f'cat {H}/evidence/kani-{n}-native/out.log');assert q.returncode==0,q.stderr;out=q.stdout;(d/'out.log').write_text(out)
record['verification_successful']='VERIFICATION:- SUCCESSFUL' in out or 'VERIFICATION SUCCESSFUL' in out
(d/'receipt.json').write_text(json.dumps(record,indent=2)+'\n');print(out[-7000:]);print('RECEIPT',json.dumps(record),flush=True)
sys.exit(p.returncode)
