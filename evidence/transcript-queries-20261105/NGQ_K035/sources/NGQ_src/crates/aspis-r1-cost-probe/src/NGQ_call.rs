use super::*;
type NGQ_Reply=Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError>;
fn NGQ_decode_oracle(blocks:&[[u8;32];8],advances:&[[u8;32];8],reply:NGQ_Reply,
 p:usize,j:usize,log:&mut(u8,u8))->NGQ_Reply {
 *log=(blocks[p][j],advances[p][j]);reply
}
fn NGQ_decode_call(blocks:[[u8;32];8],advances:[[u8;32];8],reply:NGQ_Reply,
 p:usize,j:usize,log:&mut(u8,u8))->NGQ_Reply {
 NGQ_decode_oracle(&blocks,&advances,reply,p,j,log)
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NGQ_decode_call() {
 let blocks:[[u8;32];8]=kani::any();let advances:[[u8;32];8]=kani::any();
 let q:[u32;22]=kani::any();let selected:[u8;32]=kani::any();let good:bool=kani::any();
 let tag:u8=kani::any();kani::assume(tag<3);
 let error=match tag {
  0=>aspis_core::transcript::QuerySampleError::BoundNotPowerOfTwo{bound:kani::any()},
  1=>aspis_core::transcript::QuerySampleError::CountExceedsBound{count:kani::any(),bound:kani::any()},
  _=>aspis_core::transcript::QuerySampleError::DrawLimitExhausted{accepted:kani::any(),max_draws:kani::any()},
 };
 let reply=if good {Ok((q,selected))}else{Err(error)};
 let p:usize=kani::any();let j:usize=kani::any();let i:usize=kani::any();kani::assume(p<8 && j<32 && i<22);
 let mut log=(0,0);let out=NGQ_decode_call(blocks,advances,reply,p,j,&mut log);
 let result=match out {Ok((a,s))=>good && a[i]==q[i] && s[j]==selected[j],Err(e)=>!good && e==error};
 let correct=log==(blocks[p][j],advances[p][j]) && result;
 #[cfg(not(NGQ_invert))] assert!(correct);
 #[cfg(NGQ_invert)] assert!(log.0==advances[p][j]);
}
