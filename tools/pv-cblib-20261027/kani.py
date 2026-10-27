"""One no-stub bounded P6 run, through standing capped admission tools."""
from pathlib import Path
import subprocess,sys,json,shlex
root=Path(__file__).resolve().parents[2];name,harness=sys.argv[1:3];project=sys.argv[3] if len(sys.argv)>3 else 'probe'
assert project in ('probe','standalone','sha2','block-buffer')
base='/home/dombarker/project-offloads/codex-pv-cblib-20261027';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy';out=root/'evidence/pv-cblib-20261027'/name;out.mkdir(exist_ok=True)
tally=root/'evidence/pv-cblib-20261027/TALLY.json';t=json.loads(tally.read_text());assert len(t['kani_charged'])<10 and name not in t['kani_charged']
def ssh(c):return subprocess.run(['ssh','dombarker@100.108.41.90',c],text=True,capture_output=True)
p=ssh(f'mkdir -p {base}/{name}; python3 {gate}/reservation.py {base}/{name}/admission-before.json > {base}/{name}/reservation.log 2>&1; cat {base}/{name}/reservation.log');(out/'admission-transport.log').write_text(p.stdout+p.stderr)
if p.returncode or not json.loads(p.stdout)['allowed']:sys.exit(78)
cmd=['timeout','180','taskset','--cpu-list','0-3','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','CARGO_BUILD_JOBS=4','CARGO_PROFILE_DEV_OPT_LEVEL=3',*(['CARGO_PROFILE_DEV_OVERFLOW_CHECKS=false'] if project=='sha2' else []),'RUSTFLAGS=--cfg kani',f'CARGO_TARGET_DIR={base}/kani-target','cargo','kani','--manifest-path',base+('/source/crates/aspis-r1-cost-probe/Cargo.toml' if project=='probe' else '/sha2-vendor/Cargo.toml' if project=='sha2' else '/block-buffer-vendor/Cargo.toml' if project=='block-buffer' else '/kani-proof/Cargo.toml'),*(['--features','ct-host-prover'] if project=='probe' else []),'--lib','--exact','--harness',harness,'--solver','kissat','--no-assertion-reach-checks','--output-format','terse','-j','4','-Z','unstable-options','--cbmc-args','--unwinding-assertions']
receipt=dict(target=cmd,harness=harness,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),expected_phase=('optimized compilation then symbolic 1024-element QM31 copy/conversion and arbitrary output coordinate' if 'op36' in harness else 'optimized compilation then named bounded library/reference equivalence: '+harness)+('; frozen release wrapping-overflow profile; shipped CPU compression selection, no force-soft' if project=='sha2' else ''),print_axioms='N/A Kani',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
assert not (out/'target.json').exists();(out/'target.json').write_text(json.dumps(receipt,indent=2)+'\n')
(out/'harness.rs.txt').write_text((root/'crates/aspis-r1-cost-probe/src/host_commitment.rs').read_text().split('#[cfg(kani)]\nmod pv_cblib_library_checks',1)[1] if project=='probe' else (root/'tools/pv-cblib-20261027/sha2-harness.rs').read_text() if project=='sha2' else (root/'tools/pv-cblib-20261027/block-buffer-harness.rs').read_text() if project=='block-buffer' else (root/'tools/pv-cblib-20261027/kani-lib.rs').read_text())
run=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',gate+'/barrier.py',base+'/'+name+'/admission-barrier.json','/usr/bin/time','-v','-o',base+'/'+name+'/time.log',*cmd]
p=ssh(shlex.join(run)+f' > {base}/{name}/output.log 2>&1');(out/'transport.log').write_text(p.stdout+p.stderr)
subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/collect_native.py'),name,'source/crates/aspis-r1-cost-probe/src/host_commitment.rs','kani-proof/lib.rs','kani-proof/Cargo.toml','kani-proof/Cargo.lock','source/Cargo.lock','sha2-vendor/src/core_api.rs','sha2-vendor/Cargo.toml','block-buffer-vendor/src/sealed.rs','block-buffer-vendor/Cargo.toml','block-buffer-vendor/Cargo.lock'],check=True)
r=json.loads((out/'collected-receipt.json').read_text());r.update(receipt);(out/'collected-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
if r['attempt_charged']:t['kani_charged'].append(name);tally.write_text(json.dumps(t,indent=2)+'\n')
print(r['exit'])
sys.exit(int(r['exit']) if r['exit'] is not None else 78)
