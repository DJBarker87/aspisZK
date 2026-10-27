"""Execute one named mask P6 harness through the standing host admission gate."""
from pathlib import Path
import subprocess,shlex,json,sys
root=Path(__file__).resolve().parents[2]
name,harness=sys.argv[1:3]
base='/home/dombarker/project-offloads/codex-pv-cb-20261026'
scanner='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py'
local=root/'evidence/pv-cb-20261026'/name;local.mkdir(exist_ok=True)
assert not (local/'target.json').exists()
def ssh(cmd):return subprocess.run(['ssh','dombarker@100.108.41.90',cmd],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
dest=base+'/'+name
r=ssh(f'mkdir -p {dest}; python3 {scanner} {dest}/admission-before.json > {dest}/reservation.log 2>&1')
(local/'reservation-transport.log').write_text(r.stdout)
if r.returncode:print(name,'reservation refused',r.returncode);sys.exit(r.returncode)
# Sync only proof inputs after admission and before compiling this one gate.
for relative in ['step-proof/Cargo.toml','step-proof/lib.rs','step-proof/owned_points.rs','step-proof/owned_wide_new.rs','step-proof/owned_compress.rs','step-proof/owned_pole.rs','source-proof/lib.rs','source-proof/owned_circle.rs']:
 subprocess.run(['scp',str(root/'tools/pv-cb-20261026'/relative),'dombarker@100.108.41.90:'+base+'/'+relative],check=True)
cmd=['taskset','--cpu-list','0-3','timeout','180','env','PATH=/home/dombarker/.cargo/bin:/home/dombarker/.local/bin:/usr/local/bin:/usr/bin:/bin',f'CARGO_TARGET_DIR={base}/source-kani-target','RUSTFLAGS=--cfg kani','/home/dombarker/.cargo/bin/cargo','kani','--manifest-path',base+'/step-proof/Cargo.toml','--lib','--harness','checks::'+harness,'--solver','kissat','--output-format','terse','-j','4']
meta=dict(target=cmd,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),print_axioms='N/A Kani; separate Lean source/axioms receipts',harness=harness,no_stubs=True,expected_time='cached optimized compilation, then CBMC proof generation for this one named harness',configuration_change='Restrict CPU affinity to four host CPUs to bound compiler thread fanout within TasksMax64; no cap increase',profile='step-proof profile.dev opt-level3, overflow-checks=false, debug-assertions=false; source uses explicit wrapping CT arithmetic')
(local/'target.json').write_text(json.dumps(meta,indent=2)+'\n')
args=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',dest+'/time.log',*cmd]
r=ssh(shlex.join(args)+' > '+dest+'/output.log 2>&1')
(local/'transport.log').write_text(r.stdout)
subprocess.run([sys.executable,str(root/'tools/pv-cb-20261026/collect_native.py'),name,'step-proof/Cargo.toml','step-proof/lib.rs','step-proof/owned_compress.rs','step-proof/owned_pole.rs','step-proof/Cargo.lock','source/Cargo.lock','source-proof/owned_circle.rs','source/crates/aspis-r1-cost-probe/src/sampler.rs','source/crates/aspis-r1-cost-probe/src/ct_pole.rs','source/crates/aspis-core/src/circle.rs','source/crates/aspis-core/src/transcript.rs','step-proof/reference_steps.rs','step-proof/captured_mask.rs','step-proof/owned_points.rs','step-proof/owned_wide_new.rs','source-proof/owned.rs','source/crates/aspis-core/src/state_only_hiding.rs','source/crates/aspis-core/src/state_only_prefix.rs','source/crates/aspis-core/src/field.rs','source/crates/aspis-core/src/field/wide_exact.rs'],check=True)
p=local/'collected-receipt.json';data=json.loads(p.read_text());data.update(meta);data['source_identity']='Pinned shipped crates unchanged; cfg(kani)-only proof inputs and exact source capture identified by per-run hashes. Source revision is HEAD plus the recorded uncommitted proof inputs.';p.write_text(json.dumps(data,indent=2)+'\n')
print(name,'exit',data['exit']);sys.exit(r.returncode)
