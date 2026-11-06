use super::*;
#[allow(non_snake_case)]
mod kmx { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../NKV_fragments.rs"));

#[derive(Clone,Copy)]
struct ParentOracle<'a> {
 phase:&'a core::cell::Cell<usize>,
 replies:[u8;3],roots:[[u8;32];3],queries:[u32;22],batch:usize,
 proof:*const u8,width:usize,j:usize,k:usize,
 post_i:&'a core::cell::Cell<u32>,post_v:&'a core::cell::Cell<u8>,
}
impl Digest32 for ParentOracle<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let phase=self.phase.get(); let tree=phase/2;
  assert!(tree<3); self.phase.set(phase+1);
  let mut reply=[0u8;32];
  if phase%2==0 {
   assert_eq!(parts.len(),7);
   assert_eq!(parts[0].as_ptr(),self.proof);assert_eq!(parts[0].len(),self.width);
   assert_eq!(parts[1],&self.roots[tree]);
   assert_eq!(parts[2],&self.batch.to_le_bytes());assert_eq!(parts[3],&tree.to_le_bytes());
   assert_eq!(parts[4].len(),88);
   for i in 0..22 { assert_eq!(&parts[4][4*i..4*i+4],&self.queries[i].to_le_bytes()); }
   assert_eq!(parts[5].len(),64);assert_eq!(parts[6].len(),512);
   let j=self.j;let k=self.k;
   let before_i=u32::from_le_bytes(parts[5][4*j..4*j+4].try_into().unwrap());let before_v=parts[6][32*j+k];
   assert_eq!(before_i,if tree==0 {0}else{self.post_i.get()});
   assert_eq!(before_v,if tree==0 {0}else{self.post_v.get()});
   reply[0]=self.replies[tree];reply[1]=self.j as u8;reply[2]=self.k as u8;
  } else {
   assert_eq!(parts.len(),2);
   let j=self.j;let k=self.k;
   self.post_i.set(u32::from_le_bytes(parts[0][4*j..4*j+4].try_into().unwrap()));self.post_v.set(parts[1][32*j+k]);
  }
  reply
 }
}
fn logged_tree<H:Digest32>(proof:&[u8],queries:[u32;22],root:[u8;32],batch:usize,tree:usize,idx:&mut[u32;16],val:&mut[[u8;32];16],hash:H)->Result<(),Error> {
 // Log before havoc, on the SAME arrays and decoded call arguments.
 let queries_bytes=unsafe{core::slice::from_raw_parts(queries.as_ptr()as *const u8,88)};
 let idx_bytes=unsafe{core::slice::from_raw_parts(idx.as_ptr()as *const u8,64)};
 let val_bytes=unsafe{core::slice::from_raw_parts(val.as_ptr()as *const u8,512)};
 let reply=hash.digest(&[proof,&root,&batch.to_le_bytes(),&tree.to_le_bytes(),queries_bytes,idx_bytes,val_bytes]);
 *idx=kani::any();*val=kani::any();
 let idx_after=unsafe{core::slice::from_raw_parts(idx.as_ptr()as *const u8,64)};
 let val_after=unsafe{core::slice::from_raw_parts(val.as_ptr()as *const u8,512)};
 hash.digest(&[idx_after,val_after]);
 match reply[0] {0=>Ok(()),1=>Err(Error::Parse),_=>Err(Error::Merkle)}
}
#[kani::proof]
#[kani::unwind(600)]
#[kani::stub(batch_tree,logged_tree)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn values_calls() {
 let proof:[u8;1]=kani::any();let queries:[u32;22]=kani::any();let roots:[[u8;32];3]=kani::any();let batch:usize=kani::any();kani::assume(batch<2);
 let replies:[u8;3]=kani::any();kani::assume(replies[0]<3&&replies[1]<3&&replies[2]<3);
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16&&k<32);
 let phase=core::cell::Cell::new(0);let post_i=core::cell::Cell::new(0);let post_v=core::cell::Cell::new(0);
 let oracle=ParentOracle{phase:&phase,replies,roots,queries,batch,proof:proof.as_ptr(),width:proof.len(),j,k,post_i:&post_i,post_v:&post_v};
 let out=batch_merkle_values(&proof,queries,roots,batch,oracle);
 let entered=if replies[0]!=0 {1}else if replies[1]!=0 {2}else{3};
 assert_eq!(phase.get(),2*entered);
 let code=if replies[0]!=0 {replies[0]}else if replies[1]!=0 {replies[1]}else{replies[2]};
 let exact=match code {0=>out.is_ok(),1=>matches!(out,Err(Error::Parse)),_=>matches!(out,Err(Error::Merkle))};
 #[cfg(not(NKV_invert))] assert!(exact);
 #[cfg(NKV_invert)] assert!(!exact);
}
