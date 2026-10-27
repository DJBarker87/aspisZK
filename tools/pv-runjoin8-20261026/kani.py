#!/usr/bin/env python3
"""One planned bounded source verification, using the retained own workspace."""
import hashlib,json,pathlib,shlex,subprocess,sys,time
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-runjoin8-20261026'
flag=pathlib.Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/pv-host-restored.flag')
assert flag.is_file(),'host rebuild gate closed'
number=int(sys.argv[1]);assert 1<=number<=8
plan=json.loads((e/'kani-planned.json').read_text());harness=plan['harnesses'][number-1]['name']
log=e/'kani-invocations.jsonl';previous=[json.loads(s) for s in log.read_text().splitlines()] if log.exists() else []
assert len(previous)<8 and all(p['number']!=number for p in previous)
host='dombarker@100.108.41.90';job='/home/dombarker/project-offloads/codex-pv-runjoin-20261026';frozen=job+'/frozen'
name=f'pv8-runjoin-kani-{number:02d}';out=job+'/evidence/'+name
suffix=sys.argv[2] if len(sys.argv)>2 else 'a'
def ssh(cmd):return subprocess.run(['ssh','-o','BatchMode=yes',host,cmd],capture_output=True,text=True)
res=f'{job}/evidence/{name}-reservation-{suffix}'
r=ssh(f'python3 {job}/reservation-existing.py {res}.json > {res}.log 2>&1\ncat {res}.log')
(e/f'{name}-reservation-{suffix}.log').write_text(r.stdout+r.stderr)
try:admission=json.loads(r.stdout.strip().splitlines()[-1])
except Exception:print(r.stdout+r.stderr,flush=True);sys.exit(79)
if not admission.get('allowed'):
 (e/f'{name}-refusal-{suffix}.json').write_text(json.dumps(admission,indent=2)+'\n')
 print('RESERVATION REFUSED: '+json.dumps(admission),flush=True);sys.exit(78)
for ext in ['json','log']:subprocess.run(['scp','-q',f'{host}:{res}.{ext}',str(e/f'{name}-reservation-{suffix}.{ext}')],check=True)
paths=['crates/aspis-statement/src/pool_v1/pair_trace.rs','crates/aspis-statement/src/pool_v1/pair_trace_pv_runjoin8_roots.rs']
for p in paths:subprocess.run(['scp','-q',str(root/p),f'{host}:{frozen}/{p}'],check=True)
subprocess.run(['scp','-q',str(root/'tools/pv-runjoin8-20261026/kani-receipt.py'),f'{host}:{job}/evidence/pv8-kani-receipt.py'],check=True)
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
command=['systemd-run','--user','--scope','--quiet','--unit='+name,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','env','PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_TARGET_DIR='+job+'/target','CARGO_BUILD_JOBS=4','CARGO_PROFILE_DEV_OPT_LEVEL=3','RUSTFLAGS=-C opt-level=3 -Z mir-opt-level=4 -Z inline-mir=yes -C link-arg=-Wl,--threads=4','PV8_SOURCE_DIR='+frozen,'python3',job+'/evidence/pv8-kani-receipt.py',out,'timeout','180','cargo','kani','--no-assertion-reach-checks','-Z','stubbing','-Z','function-contracts','-Z','unstable-options','-p','aspis-statement','--lib','-j','4','--exact','--harness',harness,'--output-format','terse','--cbmc-args','--unwinding-assertions','--slice-formula']
record=dict(number=number,harness=harness,source_revision=revision,command=command,source_sha256={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths},stubs=[],expected_time=plan['expected_time'])
with log.open('a') as f:f.write(json.dumps(record)+'\n')
print('CHARGED KANI '+json.dumps(record),flush=True)
r=ssh(shlex.join(command));(e/f'{name}-scope.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr,flush=True)
local_out=e/name;local_out.mkdir(exist_ok=True)
for filename in ['receipt.json','out.log']:
 subprocess.run(['scp','-q',f'{host}:{out}/{filename}',str(local_out/filename)],check=True)
receipt=e/name/'receipt.json'
if receipt.exists():
 data=json.loads(receipt.read_text());data.update(number=number,harness=harness,source_revision=revision,source_snapshot=paths)
 receipt.write_text(json.dumps(data,indent=2)+'\n')
state=ssh(f'systemctl --user show {name}.scope -p ActiveState -p SubState')
if 'ActiveState=active' in state.stdout:
 ssh(f'systemctl --user stop {name}.scope');state=ssh(f'systemctl --user show {name}.scope -p ActiveState -p SubState')
(e/f'{name}-ended.log').write_text(state.stdout+state.stderr)
assert 'ActiveState=active' not in state.stdout
sys.exit(r.returncode)
