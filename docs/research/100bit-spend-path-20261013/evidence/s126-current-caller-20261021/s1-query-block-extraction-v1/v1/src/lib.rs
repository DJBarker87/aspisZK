#![no_std]
extern crate alloc;
pub fn owned_block(mut accepted:[u32;22],mut len:usize,mut draws:usize,block:&[u8;32])->([u32;22],usize,usize,bool){
 let mut i=0;
 while i<8{
  if len==22 || draws==64{return(accepted,len,draws,true);}
  let off=4*i;let candidate=u32::from_le_bytes([block[off],block[off+1],block[off+2],block[off+3]])&((1u32<<18)-1);
  draws+=1;let mut j=0;let mut found=false;
  while j<len{if accepted[j]==candidate{found=true;break;}j+=1;}
  if !found{accepted[len]=candidate;len+=1;}
  i+=1;
 }
 (accepted,len,draws,false)
}
