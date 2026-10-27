"""Instrument host scratch only, restore exact source bytes, then count coin0 fixtures."""
from pathlib import Path
import subprocess,json,hashlib,os,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-integ4-20261027');S=D/'source';C=S/'crates/aspis-r1-cost-probe';O=D/'batch1-counts';O.mkdir()
paths=[C/'src'/n for n in ['lib.rs','prover_helper_sum.rs','prover_powers.rs','ct_pole.rs']]+[C/'examples/prover_rw_gate.rs']
original={p:p.read_bytes() for p in paths}
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(D/'combined/candidate/native-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
try:
 p=paths[0];p.write_text(p.read_text()+'''\n#[cfg(feature="prover")]
pub mod pv_b1_counts {
 use core::sync::atomic::{AtomicU64,Ordering};
 static C:[AtomicU64;3]=[const{AtomicU64::new(0)};3];
 pub fn hit(i:usize){C[i].fetch_add(1,Ordering::Relaxed);}
 pub fn reset(){for c in &C{c.store(0,Ordering::Relaxed);}}
 pub fn counts()->[u64;3]{core::array::from_fn(|i|C[i].load(Ordering::Relaxed))}
}\n''')
 for p,needle,index in [(paths[1],'pub fn state_only_copy_helper_sum(h1: &[QM31]) -> Option<QM31> {',0),(paths[2],'pub fn powers<const N: usize>(x: E) -> [E; N] {',1),(paths[3],'pub(crate) fn all_slots_clear(values: &[[[QM31; 2]; 2]], masks: &[u16; 64], chi: QM31) -> bool {',2)]:
  t=p.read_text();assert t.count(needle)==1;p.write_text(t.replace(needle,needle+f'\ncrate::pv_b1_counts::hit({index});'))
 p=paths[-1];t=p.read_text();assert t.count('let started = Instant::now();')==1
 t=t.replace('let started = Instant::now();','aspis_r1_cost_probe::pv_b1_counts::reset();\n let started = Instant::now();').replace('let seconds = started.elapsed().as_secs_f64();','let seconds = started.elapsed().as_secs_f64();\n let op_counts=aspis_r1_cost_probe::pv_b1_counts::counts();').replace('"callbacks":callbacks,','"batch1_counts_230_254_258":op_counts,"callbacks":callbacks,');p.write_text(t)
 manifest=[]
 for p,b in original.items():
  manifest.append(dict(path=str(p.relative_to(S)),original_sha256=hashlib.sha256(b).hexdigest(),instrumented_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
  q=O/(p.name+'.instrumented.txt');q.write_bytes(p.read_bytes())
 (O/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 cmd=['taskset','--cpu-list','0-3','cargo','build','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--example','prover_rw_gate','--features','optimized-terminal,r1p-check,ct-host-prover']
 (O/'command.json').write_text(json.dumps(dict(command=cmd,env={k:env[k] for k in ['CARGO_TARGET_DIR','RUSTFLAGS']},source_revision=(D/'source-revision.txt').read_text().strip()),indent=2))
 subprocess.run(cmd,cwd=S,env=env,check=True)
 binary=Path(env['CARGO_TARGET_DIR'])/'release/examples/prover_rw_gate';(O/'bin').mkdir();shutil.copy2(binary,O/'bin/prover_rw_gate')
 (O/'binary.json').write_text(json.dumps(dict(sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),bytes=binary.stat().st_size),indent=2))
finally:
 for p,b in original.items():p.write_bytes(b)
 restored={str(p.relative_to(S)):p.read_bytes()==b for p,b in original.items()}
 (O/'restored.json').write_text(json.dumps(restored,indent=2));assert all(restored.values())
subprocess.run([str(O/'bin/prover_rw_gate'),str(O/'fixtures'),'0','1'],check=True)
