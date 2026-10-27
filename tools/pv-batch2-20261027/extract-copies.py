"""Measure actual applied sources, unchanged pinned Charon/Aeneas, one scope."""
from pathlib import Path
import subprocess,json,time,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');S=H/'candidate/src';D=H/'extraction';D.mkdir(exist_ok=False)
P=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools')
(D/'tool-pins.json').write_text(json.dumps({n:hashlib.sha256((P/n).read_bytes()).hexdigest() for n in ['charon','aeneas']},indent=2)+'\n')
(D/'source-pins.json').write_text(json.dumps({str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [S/'crates/aspis-r1-cost-probe/src'/n for n in ['host_sampler.rs','host_weights.rs']]},indent=2)+'\n')
def run(label,cmd):
 O=D/label;O.mkdir();(O/'command.json').write_text(json.dumps(cmd,indent=2)+'\n');start=time.monotonic()
 with (O/'output.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=S,stdout=f,stderr=subprocess.STDOUT)
 (O/'receipt.json').write_text(json.dumps(dict(exit=r.returncode,wall_seconds=time.monotonic()-start,source_revision='5b92d4aa185486cc735c0a3eb75a3024171ca482',print_axioms='N/A extraction',time_log=(O/'time.log').read_text()),indent=2)+'\n');print(label,r.returncode,flush=True);return r.returncode
for op,mod,fn in [(249,'host_sampler','gamma_sample'),(250,'host_sampler','ordinary_sample'),(251,'host_weights','Weights::materialize'),(252,'host_weights','Weights::new'),(253,'host_weights','Weights::raw')]:
 llbc=D/f'PV_B2_{op}.llbc';out=D/f'generated-{op}';out.mkdir()
 cmd=['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','CARGO_TARGET_DIR='+str(H/'charon-target'),str(P/'charon'),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::'+mod+'::'+fn,'--include','aspis_r1_cost_probe::'+mod+'::*','--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--release','--offline','--lib','--jobs','4','--features','optimized-terminal,r1p-check,ct-host-prover']
 if run(f'charon-{op}-001',cmd):continue
 run(f'aeneas-{op}-001',['timeout','180',str(P/'aeneas'),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_B2_{op}','-dest',str(out),'-split-files','-emit-json',str(llbc)])
