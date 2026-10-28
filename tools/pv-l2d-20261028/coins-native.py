"""Freeze Coins and validate finite runs; no capped-loop or IID claim."""
from pathlib import Path
import subprocess,hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028';P=R/'tools/pv-l2d-20261028/coins-native';(P/'src').mkdir(parents=True,exist_ok=True)
s=(R/'crates/aspis-r1-cost-probe/src/sim.rs').read_text();a=s.index('struct Coins {');b=s.index('\nfn concat(',a);body=s[a:b].strip()
assert '#[cfg' not in body and 'cfg!' not in body
h=(R/'crates/aspis-prover/src/lib.rs').read_text();a=h.index('pub fn host_hashv(');b=h.index('\npub const HOST_HASH',a);host=h[a:b].strip()
raw='''use std::cell::{Cell,RefCell};
thread_local! {static CUT:Cell<Option<usize>>=const{Cell::new(None)};static CALLS:Cell<usize>=const{Cell::new(0)};static LOG:RefCell<Vec<Vec<Vec<u8>>>>=const{RefCell::new(Vec::new())};}
const HOST_HASH:fn(&[&[u8]])->[u8;32]=observed_hash;
fn observed_hash(p:&[&[u8]])->[u8;32] {
 LOG.with(|l|l.borrow_mut().push(p.iter().map(|x|x.to_vec()).collect()));
 let at=CALLS.with(|c|{let n=c.get();c.set(n+1);n});
 match CUT.with(|c|c.get()) {None=>host_hashv(p),Some(n)=>if at<n {[0;32]} else {[13;32]}}
}
fn reset(cut:Option<usize>){CUT.with(|c|c.set(cut));CALLS.with(|c|c.set(0));LOG.with(|l|l.borrow_mut().clear());}
'''+host+'\n'+body+'''
fn check(seed:[u8;32],attempt:u32,stream:u8,start:u64,cut:Option<usize>)->usize {
 reset(cut);let mut c=Coins::new(seed,attempt,stream);c.next=start;
 let got=c.nonzero();let n=CALLS.with(|c|c.get());
 assert_eq!(n,cut.map(|x|x+1).unwrap_or(1));
 assert_eq!(c.seed,seed);assert_eq!(c.attempt,attempt);assert_eq!(c.stream,stream);assert_eq!(c.next,start.wrapping_add(n as u64));
 let frames=LOG.with(|l|l.borrow().clone());
 for i in 0..n {
  let frame=vec![b"UNPROVED:R1:SIM:COIN".to_vec(),seed.to_vec(),attempt.to_le_bytes().to_vec(),vec![stream],start.wrapping_add(i as u64).to_le_bytes().to_vec()];
  assert_eq!(frames[i],frame);
 }
 let expected=match cut {Some(_)=>[13;32],None=>host_hashv(&[b"UNPROVED:R1:SIM:COIN",&seed,&attempt.to_le_bytes(),&[stream],&start.to_le_bytes()])};
 assert_eq!(got,expected);assert_ne!(got,[0;32]);1
}
fn main(){
 let mut checks=0;
 for k in 0..16u8 {for attempt in [0,u32::MAX] {for stream in [0,3,u8::MAX] {for counter in [0,1,u64::MAX-1,u64::MAX] {for cut in 0..33 {
  checks+=check([k;32],attempt,stream,counter,Some(cut));
 }}}}}
 for k in 0..64u8 {checks+=check([k;32],k as u32,k%4,0,None);}
 if std::env::args().any(|x|x=="negative") {reset(Some(0));let mut c=Coins::new([0;32],0,0);assert_eq!(c.nonzero(),[0;32],"matched false nonzero control");}
 println!("{{\\"finite_runs\\":{},\\"actual_sha_cases\\":64,\\"failed\\":0}}",checks);
}
'''
# The generated Rust string must retain literal JSON quotes.
(P/'src/main.rs').write_text(raw)
(P/'Cargo.toml').write_text('[package]\nname="pv-l2d-coins-native"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[dependencies]\nsha2="=0.10.9"\n')
(E/'coins-native-freeze.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_path='crates/aspis-r1-cost-probe/src/sim.rs',body_sha256=hashlib.sha256(body.encode()).hexdigest(),harness_sha256=hashlib.sha256(raw.encode()).hexdigest(),source_body_cfg_invariant=True,profile='release: += counter wraps; no overflow-check override',toolchain='1.94.1',evidence_class='finite native validation; synthetic rejection hashes separate from 64 actual SHA cases',not_proved=['termination on every seed','same RunJoin joint history','std array inequality implementation trace']),indent=2)+'\n')
# Reuse the admission and exact dependency archive checking workflow.
for before,after in [('expander-cargo-run.py','coins-cargo-run.py'),('expander-run.py','coins-run.py')]:
 s=(R/'tools/pv-l2d-20261028'/before).read_text().replace('expander-v3','coins-v1').replace('expander','coins')
 s=s.replace("z=next(p for p in meta['packages'] if p['name']=='zeroize');assert z['version']=='1.9.0'", "z=next(p for p in meta['packages'] if p['name']=='sha2');assert z['version']=='0.10.9'")
 (R/'tools/pv-l2d-20261028'/after).write_text(s)
print('frozen exact Coins source; external finite prefix gate prepared')
