"""Isolated optimized dispatch experiment, using the standing admission tools.
Does not modify the prover workspace or release configuration. One scope/run.
"""
from pathlib import Path
import subprocess,sys,json,shlex,hashlib,re
root=Path(__file__).resolve().parents[2];base='/home/dombarker/project-offloads/codex-pv-cblib-20261027';host='dombarker@100.108.41.90';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
label=sys.argv[1];out=root/'evidence/pv-cblib-20261027'/label;out.mkdir(exist_ok=True)
def ssh(c):return subprocess.run(['ssh',host,c],text=True,capture_output=True)
r=ssh(f'mkdir -p {base}/{label}; python3 {gate}/reservation.py {base}/{label}/admission-before.json > {base}/{label}/reservation.log 2>&1; cat {base}/{label}/reservation.log');(out/'admission-transport.log').write_text(r.stdout+r.stderr)
if r.returncode or not json.loads(r.stdout)['allowed']:sys.exit(78)
if label=='dispatch-build-auto':
 ssh(f'mkdir -p {base}/dispatch-bench')
 for name in ('Cargo.toml','main.rs'):
  subprocess.run(['scp',str(root/'tools/pv-cblib-20261027/dispatch-bench'/name),f'{host}:{base}/dispatch-bench/{name}'],check=True)
mode=sys.argv[2]
env=['env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS=4',f'CARGO_TARGET_DIR={base}/dispatch-target']
if mode.startswith('build'):
 cmd=['timeout','900',*env,'cargo','build','--release','--offline','-j','4','--manifest-path',base+'/dispatch-bench/Cargo.toml','--features','count'+(',soft' if mode=='build-soft' else '')]
 phase='optimized dependency compilation and linking; no proof generation'
else:
 cmd=['timeout','900','taskset','--cpu-list','0-3',base+'/dispatch-target/release/dispatch-bench',*sys.argv[3:]]
 phase='one deterministic fixture SHA callback census; no timing gate' if mode=='count' else 'seven per-call SHA microbenchmark batches, optimized release; no timing gate'
receipt=dict(target=cmd,expected_phase=phase,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_files={name:hashlib.sha256((root/'tools/pv-cblib-20261027/dispatch-bench'/name).read_bytes()).hexdigest() for name in ('Cargo.toml','main.rs')},print_axioms='N/A Rust measurement',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
assert not (out/'target.json').exists();(out/'target.json').write_text(json.dumps(receipt,indent=2)+'\n')
run=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',gate+'/barrier.py',base+'/'+label+'/admission-barrier.json','/usr/bin/time','-v','-o',base+'/'+label+'/time.log',*cmd]
r=ssh(shlex.join(run)+f' > {base}/{label}/output.log 2>&1');(out/'transport.log').write_text(r.stdout+r.stderr)
subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/collect_native.py'),label,'dispatch-bench/Cargo.toml','dispatch-bench/Cargo.lock','dispatch-bench/main.rs'],check=True)
p=out/'collected-receipt.json';row=json.loads(p.read_text());row.update(receipt)
meta=ssh(f'sha256sum {base}/dispatch-target/release/dispatch-bench; stat -c %s {base}/dispatch-target/release/dispatch-bench; /home/dombarker/.cargo/bin/rustc -vV; uname -m')
row['binary_toolchain']=meta.stdout;row['binary_toolchain_stderr']=meta.stderr;p.write_text(json.dumps(row,indent=2)+'\n');print(row['exit']);sys.exit(int(row['exit']) if row['exit'] is not None else 78)
