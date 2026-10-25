#![no_std]
extern crate alloc;
use aspis_core::transcript::QuerySampleError;
// Same complete state fields as the shipped private QueryScan, with explicit
// owned array operations so the reference can be extracted to Lean.
#[derive(Default)]
struct OwnedScan { accepted:[u32;22], accepted_len:usize, draws:usize }
fn owned_pairs(blocks:&[[u8;32];8],advances:&[[u8;32];8])->Result<([u32;22],[u8;32]),QuerySampleError>{
 let mut scan=OwnedScan::default();let mut selected=advances[7];let mut k=0;
 while k<8{
  let mut i=0;let mut stopped=false;
  while i<8{
   if scan.accepted_len==22 || scan.draws==64 {stopped=true;break;}
   let off=4*i;let candidate=u32::from_le_bytes([blocks[k][off],blocks[k][off+1],blocks[k][off+2],blocks[k][off+3]])&((1u32<<18)-1);
   scan.draws+=1;let mut j=0;let mut found=false;
   while j<scan.accepted_len {if scan.accepted[j]==candidate{found=true;}j+=1;}
   if !found{scan.accepted[scan.accepted_len]=candidate;scan.accepted_len+=1;}
   i+=1;
  }
  if stopped{selected=advances[k];break;}
  k+=1;
 }
 if scan.accepted_len==22{Ok((scan.accepted,selected))}
 else{Err(QuerySampleError::DrawLimitExhausted{accepted:scan.accepted_len,max_draws:64})}
}
#[cfg(kani)]mod proofs{
 use super::*;
 #[kani::proof]#[kani::unwind(24)]
 fn full_pairs_value_equal(){
  let blocks=kani::any::<[[u8;32];8]>();let advances=kani::any::<[[u8;32];8]>();
  let actual=aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances);
  let reference=owned_pairs(&blocks,&advances);
  match(actual,reference){
   (Ok((a,s)),Ok((b,t)))=>{let mut i=0;while i<22{assert!(a[i]==b[i]);i+=1;}i=0;while i<32{assert!(s[i]==t[i]);i+=1;}kani::cover!(true,"actual andreference accepted");},
   (Err(a),Err(b))=>{assert!(a==b);kani::cover!(true,"actual andreference rejected");},
   _=>assert!(false,"complete native Result mismatch"),
  }
 }
}
