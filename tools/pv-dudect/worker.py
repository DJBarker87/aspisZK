#!/usr/bin/env python3
"""Sequential optimized jobs and immutable identity/resource receipts."""
import os,subprocess,pathlib,json,hashlib,time,sys
B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-dudect-20261027');R=B/'src';stage=sys.argv[1];O=B/sys.argv[1];O.mkdir(exist_ok=False);stage=stage.split('@')[0]
cg=pathlib.Path('/sys/fs/cgroup'+pathlib.Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']};assert list(limits.values())==['6442450944','8589934592','0','64']
pins=json.loads((B/'source-manifest.json').read_text());assert all(hashlib.sha256((R/p).read_bytes()).hexdigest()==h for p,h in pins.items())
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_BUILD_JOBS='4',CARGO_TARGET_DIR=str(B/('harness-target' if stage=='build-harness' else 'candidate-target')))
cargo='/home/dombarker/.cargo/bin/cargo'
if stage=='build-harness':cmd=[cargo,'build','--manifest-path','tools/pv-dudect/Cargo.toml','--release','--offline','--locked','-j','4']
elif stage=='build-candidate':cmd=[cargo,'build','--manifest-path','tools/r1-cost-probe/Cargo.toml','--release','--offline','--locked','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','devnet_spend']
elif stage=='dry':cmd=['taskset','-c','2',str(B/'bin/pv-dudect'),'--dry-run','1000']
elif stage=='compare':cmd=['python3','tools/pv-dudect/compare.py',str(B/'bin/pv-dudect'),str(B/'bin/devnet_spend'),str(O)]
else:cmd=['python3','tools/pv-dudect/metadata.py',str(O)]
rec=dict(stage=stage,target=cmd,source_revision='73070ddd512bc4e79edfc0db714fb64dc74e87b8',harness_manifest_sha256=hashlib.sha256((B/'source-manifest.json').read_bytes()).hexdigest(),limits=limits,print_axioms='N/A: no Lean',expected_work='optimized compilation/linking' if stage.startswith('build') else ('tiny dry run; not a measurement' if stage=='dry' else 'static inspection'),rustc=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','-Vv'],text=True),environment={k:env[k] for k in ['RUSTFLAGS','CARGO_TARGET_DIR','CARGO_BUILD_JOBS']})
t=time.monotonic()
with (O/'stdout.log').open('w') as so,(O/'stderr.log').open('w') as se:r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=R,env=env,stdout=so,stderr=se)
rec.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,peak_rss_scope_bytes=int((cg/'memory.peak').read_text()),swap_peak_bytes=int((cg/'memory.swap.peak').read_text()))
if stage.startswith('build') and r.returncode==0:
 name='pv-dudect' if stage=='build-harness' else 'devnet_spend';binary=pathlib.Path(env['CARGO_TARGET_DIR'])/'release'/name
 (B/'bin').mkdir(exist_ok=True);import shutil;shutil.copy2(binary,B/'bin'/name)
 rec.update(binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),binary_bytes=binary.stat().st_size)
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));sys.exit(r.returncode)
