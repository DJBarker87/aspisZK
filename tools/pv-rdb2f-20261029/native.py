"""New finite native pointer/guard checks plus the unchanged original fixtures.
Optimized compilation is expected to dominate; no arithmetic elimination.
"""
from pathlib import Path
import json,hashlib,shutil,subprocess,os
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2f-20261029');old=D.with_name('codex-pv-rdb2e-20261029');P=D/'native';P.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
prior=json.loads((old/'native-inputs.json').read_text())
for r in prior['inputs']:
 p=Path(r['path']);assert sha(p)==r['sha256'],p;shutil.copyfile(p,P/p.name)
new=r'''
fn pointer_guard_audit() {
  for seed in 0..256u32 {
    let mut words: [u32;8]=core::array::from_fn(|i|seed.wrapping_add(i as u32));
    let base=words.as_mut_ptr() as usize;
    for (step,word) in words.iter_mut().rev().enumerate() {
      assert_eq!(word as *mut u32 as usize,base+4*(7-step));
      *word=word.wrapping_add(100+step as u32);
    }
    for i in 0..8 { assert_eq!(words[i],seed+i as u32+107-i as u32); }
    let mut calls=0usize;
    let output:[u32;8]=core::array::from_fn(|i| {
      assert_eq!(i,calls);
      let current_base=words.as_mut_ptr() as usize;
      for (step,word) in words.iter_mut().rev().enumerate() {
        assert_eq!(word as *mut u32 as usize,current_base+4*(7-step));
        *word=word.wrapping_add(1);
      }
      calls+=1;
      words[0]
    });
    assert_eq!(calls,8);
    for i in 0..8 { assert_eq!(output[i],seed+108+i as u32);assert_eq!(words[i],seed+115); }
  }
  println!("RDB2F pointer_guard:256 cases;18432 actual pointer-address/current-allocation stores;2048 ordered FnMut captures;all pass (finite validation)");
}
'''
main=P/'main.rs';s=main.read_text();assert 'fn main(){'in s;main.write_text(new+s.replace('fn main(){','fn main(){\n pointer_guard_audit();',1))
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target'),CARGO_BUILD_JOBS='4')
r=subprocess.run(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--format-version','1','--locked'],env=env,capture_output=True,text=True);assert r.returncode==0,r.stderr
meta=json.loads(r.stdout);nodes={p['id']:p for p in meta['resolve']['nodes']}
for r in prior['feature_checks']:assert nodes[r['id']]['features']==r['features'],r['id']
(D/'native-inputs.json').write_text(json.dumps(dict(inputs=[dict(path=str(p),sha256=sha(p))for p in P.iterdir()if p.is_file()],inherited_inputs=prior['inputs'],feature_checks=prior['feature_checks'],all_resolved_features=meta['resolve']['nodes'],toolchain=subprocess.check_output(['rustc','-Vv'],env=env,text=True),profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',evidence_class='finite validation only; new actual pointer/guard checks plus unchanged source fixtures'),indent=2))
print('Expected phase: optimized compilation then new finite current-allocation/guard checks',flush=True)
subprocess.run(['cargo','run','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--bin','associations','-j','4'],env=env,check=True)
