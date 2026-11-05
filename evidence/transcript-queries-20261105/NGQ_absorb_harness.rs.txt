use super::*;
use core::cell::Cell;
#[derive(Clone,Copy)]
struct NGQ_AbsorbOracle<'a> {
 log:&'a Cell<(usize,u8,u8,u8,u8,bool,usize)>,reply:&'a [u8;32],
 expected_payload:&'a [u8],j:usize,l:usize,
}
impl aspis_core::Digest32 for NGQ_AbsorbOracle<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(parts.len(),4);assert_eq!(parts[0].len(),32);
  assert_eq!(parts[1].len(),2);assert_eq!(parts[2].len(),4);
  self.log.set((1,parts[0][self.j],parts[1][0],parts[1][1],parts[2][self.l],
    parts[3].as_ptr()==self.expected_payload.as_ptr(),parts[3].len()));
  *self.reply
 }
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_absorb() {
 let state:[u8;32]=kani::any();let reply:[u8;32]=kani::any();
 let bytes:[u8;8192]=kani::any();let n:usize=kani::any();kani::assume(n<=8192);
 let row:u8=kani::any();kani::assume(row<=95);
 let j:usize=kani::any();let l:usize=kani::any();kani::assume(j<32 && l<4);
 let payload=&bytes[..n];let log=Cell::new((0usize,0u8,0u8,0u8,0u8,false,0usize));
 let hash=NGQ_AbsorbOracle{log:&log,reply:&reply,expected_payload:payload,j,l};
 let mut t=Transcript{state,hash};t.absorb(row,payload);
 let expected=(1,state[j],0,160+row,((n as u32)>>(8*l)) as u8,true,n);
 let correct=log.get()==expected && t.state[j]==reply[j];
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(t.state[j]==(reply[j]^1));
}
