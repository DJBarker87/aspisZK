#![no_std]
extern crate alloc;
use aspis_core::transcript::QuerySampleError;
fn owned_contains(a:&[u32;22],len:usize,candidate:u32)->bool{
 let mut j=0;while j<len{if a[j]==candidate{return true;}j+=1;}false
}
fn owned_step(mut a:[u32;22],mut len:usize,mut draws:usize,candidate:u32)->([u32;22],usize,usize,bool){
 if len==22 || draws==64{return(a,len,draws,true);}
 draws+=1;
 if !owned_contains(&a,len,candidate){a[len]=candidate;len+=1;}
 (a,len,draws,false)
}
fn owned_block(mut accepted:[u32;22],mut len:usize,mut draws:usize,block:&[u8;32])->([u32;22],usize,usize,bool){
 let mut i=0;
 while i<8{
  let off=4*i;let candidate=u32::from_le_bytes([block[off],block[off+1],block[off+2],block[off+3]])&((1u32<<18)-1);
  let (a,n,d,stop)=owned_step(accepted,len,draws,candidate);
  accepted=a;len=n;draws=d;
  if stop{return(accepted,len,draws,true);}
  i+=1;
 }
 (accepted,len,draws,false)
}

struct OwnedScan{accepted:[u32;22],accepted_len:usize,draws:usize}
pub fn pairs_reference(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),QuerySampleError>{
 let mut scan=OwnedScan{accepted:[0;22],accepted_len:0,draws:0};let mut state=advances[7];let mut k=0;
 while k<8{
  let (a,n,d,stop)=owned_block(scan.accepted,scan.accepted_len,scan.draws,&blocks[k]);
  scan=OwnedScan{accepted:a,accepted_len:n,draws:d};
  if stop{state=advances[k];break;}
  k+=1;
 }
 if scan.accepted_len==22{Ok((scan.accepted,state))}
 else{Err(QuerySampleError::DrawLimitExhausted{accepted:scan.accepted_len,max_draws:64})}
}
