"""Run one named, capped P6 harness through the standing admission/barrier tools."""
from pathlib import Path
import subprocess,sys,json,shlex,hashlib
root=Path(__file__).resolve().parents[2];name,harness=sys.argv[1:3]
base='/home/dombarker/project-offloads/codex-pv-cb3-20261026'; gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
out=root/'evidence/pv-cb3-20261026'/name;out.mkdir(exist_ok=True)
def remote(cmd):return subprocess.run(['ssh','dombarker@100.108.41.90',cmd],text=True,capture_output=True)
p=remote(f'mkdir -p {base}/{name}; python3 {gate}/reservation.py {base}/{name}/admission-before.json > {base}/{name}/reservation.log 2>&1; cat {base}/{name}/reservation.log')
(out/'admission-transport.log').write_text(p.stdout+p.stderr)
r=json.loads(p.stdout)
if not r['allowed']: print('REFUSED',r);sys.exit(78)
cmd=['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS=4','CARGO_PROFILE_DEV_OPT_LEVEL=3',f'CARGO_TARGET_DIR={base}/kani-target','cargo','kani','--manifest-path',f'{base}/source/crates/aspis-core/Cargo.toml','--features','r0,ct-host-prover','--lib','--exact','--harness',harness,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','4','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
target=dict(target=cmd,harness=harness,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),expected_phase='Optimized compilation, then complete arbitrary-field serialization comparison; no stubs, bounded shipped byte-copy loop.',print_axioms='N/A native P6 gate',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
assert not (out/'target.json').exists();(out/'target.json').write_text(json.dumps(target,indent=2)+'\n')
run=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',gate+'/barrier.py',f'{base}/{name}/admission-barrier.json','/usr/bin/time','-v','-o',f'{base}/{name}/time.log',*cmd]
p=remote(shlex.join(run)+f' > {base}/{name}/output.log 2>&1');(out/'transport.log').write_text(p.stdout+p.stderr)
subprocess.run([sys.executable,str(root/'tools/pv-cb3-20261026/collect_native.py'),name,'source/crates/aspis-core/src/field/wide_exact.rs'],check=True)
receipt=out/'collected-receipt.json';r=json.loads(receipt.read_text());r.update(target);receipt.write_text(json.dumps(r,indent=2)+'\n');print(r['exit'])
