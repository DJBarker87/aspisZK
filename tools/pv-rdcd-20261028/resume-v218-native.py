from pathlib import Path
import subprocess,os,json,hashlib,sys
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');P=D/'classification-project-fixture';base=(D/'classify-project-focused-leaves/fixture.rs.txt').read_text()
extra='''
#[test] fn mixed_range() {
 let mut cases=0;
 for start in 0usize..12 {for len in 0usize..9 {for pattern in 0usize..(1usize << len) {
  let mut r=start..start+len;let mut lo=start;let mut hi=start+len;
  for k in 0..len+2 {
   if (pattern >> (k % 9)) & 1 == 0 {let expected=if lo<hi {let x=lo;lo+=1;Some(x)}else{None};assert_eq!(r.next(),expected);}
   else {let expected=if lo<hi {hi-=1;Some(hi)}else{None};assert_eq!(r.next_back(),expected);}
   assert_eq!((r.start,r.end),(lo,hi));
  }
  assert_eq!(r.next(),None);assert_eq!(r.next_back(),None);cases+=1;
 }}}
 println!("V218 {} finite mixed front/back range histories; endpoints and exhaustion checked",cases);
}
'''
(P/'fixture.rs').write_text(base+extra)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'classification-target'),CARGO_BUILD_JOBS='4')
cmd=['cargo','test','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--locked','-j','4','--lib','mixed_range','--','--nocapture','--test-threads=1']
m=json.loads(subprocess.check_output(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--offline','--locked','--format-version','1'],env=env,text=True));nodes={x['id']:x for x in m['resolve']['nodes']}
(D/'resume-v218/native-inputs.json').write_text(json.dumps(dict(command=cmd,toolchain=subprocess.check_output(['rustc','-vV'],env=env,text=True),features=[dict(name=p['name'],version=p['version'],features=nodes[p['id']]['features']) for p in m['packages']],profile='release opt3 debug_assertions=false overflow_checks=false',fixture_sha256=hashlib.sha256((base+extra).encode()).hexdigest(),extra=extra,qualification='Finite native validation of new Range model boundary only; no Kani, no universal Rust/LLVM refinement'),indent=2)+'\n')
print('Expected time: optimized cached compilation then6132 mixed front/back finite histories',flush=True)
sys.exit(subprocess.run(cmd,env=env).returncode)
