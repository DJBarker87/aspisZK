from NCB_generate import *
p='crates/aspis-r1-cost-probe/src/transcript.rs'
t=r'''
#[cfg(kani)] mod NCB_digest_calls {
 use super::*;
 #[derive(Clone,Copy)] struct Spy;
 static mut MODE:u8=0;static mut CALLS:usize=0;static mut ROW:u8=0;static mut J:usize=0;
 static mut START:[u8;32]=[0;32];static mut REPLIES:[[u8;32];3]=[[0;32];3];
 static mut PAYLOAD:*const u8=core::ptr::null();static mut LENGTH:usize=0;
 impl Digest32 for Spy {fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{
  let c=CALLS;CALLS+=1;assert!(c<3);
  if MODE==0 {
   assert!(c==0&&parts.len()==3);assert!(parts[0]==b"UNPROVED:R1:PRIVATE-SALTED:P3");assert!(parts[1]==[2]);assert!(parts[2].len()==32&&parts[2][J]==START[J]);
  }else if c==0{
   assert!(parts.len()==4&&parts[0].len()==32&&parts[0][J]==START[J]);
   assert!(parts[1]==[0,0xa0+ROW]);assert!(parts[2].len()==4);let n=u32::from_le_bytes(parts[2].try_into().unwrap());assert!(n==LENGTH as u32);
   assert!(parts[3].len()==LENGTH&&core::ptr::eq(parts[3].as_ptr(),PAYLOAD));
  }else{
   assert!(MODE==2&&parts.len()==2);assert!(parts[0].len()==32&&parts[0][J]==REPLIES[0][J]);assert!(parts[1].len()==1&&parts[1][0]==c as u8);
  }
  REPLIES[c]
 }}}
 fn setup(mode:u8,state:[u8;32],row:u8,payload:&[u8],j:usize){unsafe{MODE=mode;CALLS=0;START=state;ROW=row;J=j;PAYLOAD=payload.as_ptr();LENGTH=payload.len();REPLIES=kani::any();}}
 #[kani::proof] #[kani::unwind(512)] ATTR
 fn seed(){assert!(cfg!(feature="private-leaf-salts"));let state:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<32);setup(0,state,0,&[],j);let out=Transcript::new(Spy,state,Variant::S2);unsafe{assert!(CALLS==1&&out.state[j]==REPLIES[0][j]);}}
 #[kani::proof] #[kani::unwind(512)] ATTR
 fn absorb(){let state:[u8;32]=kani::any();let payload:[u8;64]=kani::any();let n:usize=kani::any();kani::assume(n<=64);let j:usize=kani::any();kani::assume(j<32);let row:u8=kani::any();kani::assume(row<=95);let bytes=&payload[..n];setup(1,state,row,bytes,j);let mut t=Transcript{state,hash:Spy};t.absorb(row,bytes);unsafe{assert!(CALLS==1&&t.state[j]==REPLIES[0][j]);}}
 #[kani::proof] #[kani::unwind(512)] ATTR
 fn block(){let state:[u8;32]=kani::any();let payload:[u8;64]=kani::any();let n:usize=kani::any();kani::assume(n<=64);let j:usize=kani::any();kani::assume(j<32);let row:u8=kani::any();kani::assume(row<=95);let bytes=&payload[..n];setup(2,state,row,bytes,j);let mut t=Transcript{state,hash:Spy};let out=t.block(row,bytes);unsafe{assert!(CALLS==3&&out[j]==REPLIES[1][j]&&t.state[j]==REPLIES[2][j]);}}
}
'''.replace('ATTR',attrs)
emit(p,t,'NCB_transcript')
