use std::cell::{Cell,RefCell};
thread_local! {static CUT:Cell<Option<usize>>=const{Cell::new(None)};static CALLS:Cell<usize>=const{Cell::new(0)};static LOG:RefCell<Vec<Vec<Vec<u8>>>>=const{RefCell::new(Vec::new())};}
const HOST_HASH:fn(&[&[u8]])->[u8;32]=observed_hash;
fn observed_hash(p:&[&[u8]])->[u8;32] {
 LOG.with(|l|l.borrow_mut().push(p.iter().map(|x|x.to_vec()).collect()));
 let at=CALLS.with(|c|{let n=c.get();c.set(n+1);n});
 match CUT.with(|c|c.get()) {None=>host_hashv(p),Some(n)=>if at<n {[0;32]} else {[13;32]}}
}
fn reset(cut:Option<usize>){CUT.with(|c|c.set(cut));CALLS.with(|c|c.set(0));LOG.with(|l|l.borrow_mut().clear());}
pub fn host_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input);
    }
    hasher.finalize().into()
}
struct Coins { seed:[u8;32], attempt:u32, stream:u8, next:u64 }
impl Coins {
    fn new(seed:[u8;32],attempt:u32,stream:u8)->Self { Self{seed,attempt,stream,next:0} }
    fn coin(&mut self)->[u8;32] {
        let c=HOST_HASH(&[b"UNPROVED:R1:SIM:COIN",&self.seed,&self.attempt.to_le_bytes(),&[self.stream],&self.next.to_le_bytes()]);
        self.next+=1;c
    }
    fn nonzero(&mut self)->[u8;32] { loop { let c=self.coin(); if c!=[0;32] {return c;} } }
}
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
 println!("{{\"finite_runs\":{},\"actual_sha_cases\":64,\"failed\":0}}",checks);
}
