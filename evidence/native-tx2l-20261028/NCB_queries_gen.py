from NCB_generate import *
p='crates/aspis-r1-cost-probe/src/transcript.rs'
t=r'''
#[cfg(kani)] mod NCB_query_calls {
 use super::*;
 #[derive(Clone,Copy)] struct Spy;
 static mut CALLS:usize=0;static mut J:usize=0;static mut ROW:u8=0;
 static mut INITIAL:[u8;32]=[0;32];static mut REPLIES:[[u8;32];17]=[[0;32];17];
 static mut PTR:*const u8=core::ptr::null();static mut LEN:usize=0;static mut CHILD:u8=0;static mut FAIL:bool=false;static mut PICK:usize=0;
 static mut QUERY:[u32;22]=[0;22];
 impl Digest32 for Spy{fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{
  let c=CALLS;assert!(c<17);CALLS+=1;
  if c==0{assert!(parts.len()==4&&parts[0].len()==32&&parts[0][J]==INITIAL[J]);assert!(parts[1]==[0,0xa0+ROW]);assert!(parts[2].len()==4&&u32::from_le_bytes(parts[2].try_into().unwrap())==LEN as u32);assert!(parts[3].len()==LEN&&parts[3].as_ptr()==PTR);}
  else{let pair=(c-1)/2;let state=2*pair;assert!(parts.len()==2&&parts[0].len()==32&&parts[0][J]==REPLIES[state][J]);assert!(parts[1].len()==1&&parts[1][0]==if c%2==1{1}else{2});}
  REPLIES[c]
 }}}
 fn child(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError>{unsafe{
  assert!(CALLS==17&&CHILD==0);CHILD=1;
  let i:usize=kani::any();kani::assume(i<8);assert!(blocks[i][J]==REPLIES[2*i+1][J]&&advances[i][J]==REPLIES[2*i+2][J]);
  if FAIL{Err(aspis_core::transcript::QuerySampleError::DrawLimitExhausted{accepted:0,max_draws:64})}
  else{Ok((QUERY,advances[PICK]))}
 }}
'''
for mode in ['success','failure']:
 t+='#[kani::proof] #[kani::unwind(1024)]\n'+attrs+'#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,child)]\nfn '+mode+'(){\n'
 t+='''let before:[u8;32]=kani::any();let payload:[u8;64]=kani::any();let len:usize=kani::any();kani::assume(len<=64);let bytes=&payload[..len];let row:u8=kani::any();kani::assume(row<=95);let j:usize=kani::any();kani::assume(j<32);let pick:usize=kani::any();kani::assume(pick<8);
 let queries:[u32;22]=kani::any();for i in 0..22{kani::assume(queries[i]<262144);}
 unsafe{CALLS=0;J=j;ROW=row;INITIAL=before;REPLIES=kani::any();PTR=bytes.as_ptr();LEN=len;CHILD=0;PICK=pick;QUERY=queries;FAIL='''+str(mode=='failure').lower()+''';}
 let mut t=Transcript{state:before,hash:Spy};let result=t.queries(row,bytes);unsafe{assert!(CALLS==17&&CHILD==1);}
'''
 if mode=='success':t+='''let out=result.unwrap();let i:usize=kani::any();kani::assume(i<22);assert!(out[i]==queries[i]);unsafe{assert!(t.state[j]==REPLIES[2*pick+2][j]);}\n'''
 else:t+='''assert!(matches!(result,Err(crate::verifier::Error::Transcript)));unsafe{assert!(t.state[j]==REPLIES[0][j]);}\n'''
 t+='}\n'
t+='}\n';emit(p,t,'NCB_queries')
