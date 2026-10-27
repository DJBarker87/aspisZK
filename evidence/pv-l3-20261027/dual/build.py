#!/usr/bin/env python3
"""Task-specific receipt collector; called inside the prescribed scope."""
import os,sys,json,hashlib,subprocess,time
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-pv-l3-20261026'); name=sys.argv[1];R=H/('dual-'+name); O=H/('dual-evidence/'+name);O.mkdir(parents=True,exist_ok=False)
pins=json.loads((H/(name+'-source.json')).read_text())
for path,pin in pins['files'].items():
 assert hashlib.sha256((R/path).read_bytes()).hexdigest()==pin['sha256'],path
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']};assert list(limits.values())==['6442450944','8589934592','0','64'],limits
# Match the R1 receipt wrapper, with external target directories to preserve sources.
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_TARGET_DIR=str(H/'dual-target-A'))
cmd=['/home/dombarker/.cargo/bin/cargo','build','--manifest-path','tools/r1-cost-probe/Cargo.toml','--release','--offline','--locked','-j','4','--features','r1p-check','--bin','devnet_spend']
rec=dict(artifact=name,source_revision=pins['revision'],source_files=len(pins['files']),target=cmd,cwd=str(R),limits=limits,environment={k:v for k,v in env.items() if k.startswith(('CARGO','RUST')) or k=='PATH'},expected_work='optimized compilation/linking only; no binary execution, proof generation or elimination',print_axioms='N/A (no Lean)',rustc=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','-Vv'],text=True,cwd=R),cargo=subprocess.check_output(['/home/dombarker/.cargo/bin/cargo','-V'],text=True,cwd=R),cpu=subprocess.check_output(['lscpu'],text=True))
rec['label']='devnet R1 recipe, toolchain unpinned (host default '+rec['rustc'].splitlines()[0]+')';(O/'preflight.json').write_text(json.dumps(rec,indent=2)+'\n')
t=time.monotonic()
with (O/'stdout.log').open('w') as so,(O/'stderr.log').open('w') as se:ret=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=R,env=env,stdout=so,stderr=se).returncode
rec.update(exit_status=ret,wall_seconds=time.monotonic()-t,cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_peak_bytes=int((cg/'memory.swap.peak').read_text()))
B=Path(env['CARGO_TARGET_DIR'])/'release/devnet_spend'
if ret==0:
 rec.update(binary_sha256=hashlib.sha256(B.read_bytes()).hexdigest(),binary_bytes=B.stat().st_size)
 (H/'bin'/('devnet_spend-'+name)).write_bytes(B.read_bytes())
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));sys.exit(ret)
