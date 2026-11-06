#[derive(Clone,Copy)]
struct VerifyOracle<'a>{calls:&'a core::cell::Cell<usize>,root:[u8;32],nodes:&'a[u8],idx_ptr:*const u32,val_ptr:*const u8,d:usize,j:usize,k:usize,valid:bool,post_i:&'a core::cell::Cell<u32>,post_v:&'a core::cell::Cell<u8>}
impl Digest32 for VerifyOracle<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{
 let phase=self.calls.get();self.calls.set(phase+1);let mut reply=[0u8;32];
 if phase==0{
  assert_eq!(parts.len(),5);assert_eq!(parts[0],&self.root);assert_eq!(parts[1].as_ptr(),self.nodes.as_ptr());assert_eq!(parts[1].len(),self.nodes.len());
  assert_eq!(parts[2],&self.d.to_le_bytes());assert_eq!(parts[3].as_ptr(),self.idx_ptr as *const u8);assert_eq!(parts[3].len(),64);assert_eq!(parts[4].as_ptr(),self.val_ptr);assert_eq!(parts[4].len(),512);
  reply[0]=self.j as u8;reply[1]=self.k as u8;reply[2]=self.valid as u8;
 }else{
  assert_eq!(phase,1);assert_eq!(parts.len(),2);assert_eq!(parts[0].len(),4);assert_eq!(parts[1].len(),1);
  self.post_i.set(u32::from_le_bytes(parts[0].try_into().unwrap()));self.post_v.set(parts[1][0]);
 }
 reply
}}
fn logged_verify<H:Digest32>(hash:H,arity:Arity,root:&[u8;32],idx:&mut[u32;16],val:&mut[[u8;32];16],d:usize,nodes:&[u8])->bool{
 assert!(matches!(arity,Arity::Two));
 // Byte views are only a local log of the two fully initialized, padding-free arrays.
 let idx_bytes=unsafe{core::slice::from_raw_parts(idx.as_ptr() as *const u8,64)};
 let val_bytes=unsafe{core::slice::from_raw_parts(val.as_ptr() as *const u8,512)};
 let reply=hash.digest(&[root,nodes,&d.to_le_bytes(),idx_bytes,val_bytes]);let j=reply[0]as usize;let k=reply[1]as usize;assert!(j<16&&k<32);
 *idx=kani::any();*val=kani::any();
 hash.digest(&[&idx[j].to_le_bytes(),&val[j][k..k+1]]);
 reply[2]!=0
}
#[kani::proof]
#[kani::unwind(600)]
#[kani::stub(multiproof::verify_in_place,logged_verify)]
#[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
fn verify_finish(){
 let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let root:[u8;32]=kani::any();let nodes:[u8;5504]=kani::any();
 let d:usize=kani::any();let count:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let valid:bool=kani::any();kani::assume(d<=12&&count<=172&&j<16&&k<32);
 let calls=core::cell::Cell::new(0);let post_i=core::cell::Cell::new(0);let post_v=core::cell::Cell::new(0);
 let oracle=VerifyOracle{calls:&calls,root,nodes:&nodes[..32*count],idx_ptr:idx.as_ptr(),val_ptr:val.as_ptr()as *const u8,d,j,k,valid,post_i:&post_i,post_v:&post_v};
 let out=verify_finish_fragment(root,&mut idx,&mut val,d,&nodes,count,oracle);
 assert_eq!(calls.get(),2);assert_eq!(idx[j],post_i.get());assert_eq!(val[j][k],post_v.get());
 #[cfg(not(NKL_invert))] assert_eq!(out.is_ok(),valid);
 #[cfg(NKL_invert)] assert_ne!(out.is_ok(),valid);
 if !valid{assert!(matches!(out,Err(Error::Merkle)))}
}
