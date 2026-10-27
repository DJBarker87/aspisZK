"""Instrument the existing host scratch source, build optimized, restore exact bytes.
Never applied to tracked crates/. Counters include nested calls; timing is not used.
"""
from pathlib import Path
import subprocess,json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
S=H/'candidate/src'; C=S/'crates/aspis-r1-cost-probe'; O=H/'call-counts';O.mkdir(exist_ok=False)
paths=[C/'src'/n for n in ['lib.rs','host_sampler.rs','host_weights.rs','sampler.rs','weights.rs']]+[C/'examples/prover_rw_gate.rs']
original={p:p.read_bytes() for p in paths}
manifest=[]
try:
 lib=paths[0];lib.write_text(lib.read_text()+'''\n#[cfg(feature="prover")]
pub mod pv_b2_counts {
 use core::sync::atomic::{AtomicU64,Ordering};
 static C:[AtomicU64;10]=[const {AtomicU64::new(0)};10];
 pub fn hit(i:usize){C[i].fetch_add(1,Ordering::Relaxed);}
 pub fn reset(){for c in &C {c.store(0,Ordering::Relaxed);}}
 pub fn counts()->[u64;10]{core::array::from_fn(|i|C[i].load(Ordering::Relaxed))}
}\n''')
 for name,offset in [('host_sampler.rs',0),('host_weights.rs',0),('sampler.rs',5),('weights.rs',5)]:
  p=C/'src'/name;t=p.read_text()
  import re
  for op,fn in [(249,'gamma_sample'),(250,'ordinary_sample'),(251,'materialize'),(252,'new'),(253,'raw')]:
   pat=r'(pub fn '+fn+r'\([^\n]*?\{)'
   if re.search(pat,t):
    t,n=re.subn(pat,lambda m:m[1]+f'\n #[cfg(feature="prover")] crate::pv_b2_counts::hit({op-249+offset});',t,count=1);assert n==1
  p.write_text(t)
 p=paths[-1];t=p.read_text().replace('let started = Instant::now();','aspis_r1_cost_probe::pv_b2_counts::reset();\n            let started = Instant::now();').replace('let seconds = started.elapsed().as_secs_f64();','let seconds = started.elapsed().as_secs_f64();\n            let op_counts=aspis_r1_cost_probe::pv_b2_counts::counts();').replace('"callbacks":callbacks,','"op_counts_copy_then_original_249_to_253":op_counts, "callbacks":callbacks,');p.write_text(t)
 for p in paths:
  manifest.append(dict(path=str(p.relative_to(S)),original_sha256=hashlib.sha256(original[p]).hexdigest(),instrumented_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
  # Exact instrumented source is evidence outside crates/, without compiled artifacts.
  q=O/'instrumented'/p.relative_to(S);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
 (O/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 cmd=['cargo','build','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--example','prover_rw_gate','--features','optimized-terminal,r1p-check,ct-host-prover']
 subprocess.run(cmd,cwd=S,check=True)
 binary=Path('/home/dombarker/project-offloads/codex-pv-rebase-20261026/native-target/release/examples/prover_rw_gate')
 (O/'binary.json').write_text(json.dumps(dict(sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),bytes=binary.stat().st_size,command=cmd),indent=2)+'\n')
 subprocess.run([str(binary),str(O/'fixtures'),'100','1'],check=True)
finally:
 for p,b in original.items():p.write_bytes(b)
 (O/'restored.json').write_text(json.dumps({str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest()==hashlib.sha256(b).hexdigest() for p,b in original.items()},indent=2)+'\n')
