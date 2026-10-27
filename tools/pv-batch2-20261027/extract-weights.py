"""Measure actual applied sources, unchanged pinned Charon/Aeneas, one scope."""
from pathlib import Path
import subprocess,json,time,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');S=H/'candidate/src';D=H/'extraction-weights';D.mkdir(exist_ok=False)
P=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools')
(D/'tool-pins.json').write_text(json.dumps({n:hashlib.sha256((P/n).read_bytes()).hexdigest() for n in ['charon','aeneas']},indent=2)+'\n')
(D/'source-pins.json').write_text(json.dumps({str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [S/'crates/aspis-r1-cost-probe/src'/n for n in ['host_sampler.rs','host_weights.rs']]},indent=2)+'\n')
def run(label,cmd):
 O=D/label;O.mkdir();(O/'command.json').write_text(json.dumps(cmd,indent=2)+'\n');start=time.monotonic()
 with (O/'output.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=S,stdout=f,stderr=subprocess.STDOUT)
 (O/'receipt.json').write_text(json.dumps(dict(exit=r.returncode,wall_seconds=time.monotonic()-start,source_revision='5b92d4aa185486cc735c0a3eb75a3024171ca482',print_axioms='N/A extraction',time_log=(O/'time.log').read_text()),indent=2)+'\n');print(label,r.returncode,flush=True);return r.returncode
lib=S/'crates/aspis-r1-cost-probe/src/lib.rs';original=lib.read_bytes()
wrappers='\n#[cfg(feature="prover")]\npub fn pv_b2_materialize(w:&host_weights::Weights,k:aspis_core::field::WideExact,out:&mut [aspis_core::field::WideExact;1024])->Result<(),verifier::Error>{w.materialize(k,out)}\n#[cfg(feature="prover")]\npub fn pv_b2_new(v:transport::Variant,a:&[aspis_core::field::QM31;10],z:&[aspis_core::circle::SecureCirclePoint;2])->Result<host_weights::Weights,verifier::Error>{host_weights::Weights::new(v,a,z)}\n#[cfg(feature="prover")]\npub fn pv_b2_raw(w:&host_weights::Weights,kind:usize,j:usize)->aspis_core::field::QM31{w.raw(kind,j)}\n'
try:
 lib.write_bytes(original+wrappers.encode());(D/'wrapper-lib.rs.txt').write_bytes(lib.read_bytes())
 for op,fn in [(251,'pv_b2_materialize'),(252,'pv_b2_new'),(253,'pv_b2_raw')]:
  llbc=D/f'PV_B2_{op}.llbc';out=D/f'generated-{op}';out.mkdir()
  cmd=['timeout','180','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','CARGO_TARGET_DIR='+str(H/'charon-target'),str(P/'charon'),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default','--start-from','crate::'+fn,'--include','aspis_r1_cost_probe::'+fn,'--include','aspis_r1_cost_probe::host_weights::*','--include','aspis_core::field::*','--dest-file',str(llbc),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--release','--offline','--lib','--jobs','4','--features','optimized-terminal,r1p-check,ct-host-prover']
  if run(f'charon-{op}-002',cmd):continue
  run(f'aeneas-{op}-002',['timeout','180',str(P/'aeneas'),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',f'PV_B2_{op}','-dest',str(out),'-split-files','-emit-json',str(llbc)])
finally:
 lib.write_bytes(original);(D/'restored.json').write_text(json.dumps(dict(lib_restored=lib.read_bytes()==original,lib_sha256=hashlib.sha256(original).hexdigest()),indent=2)+'\n')
