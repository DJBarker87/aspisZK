// Source-ordered resume segment cuts. Frozen body: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
// Child Reader methods are local full-reply oracles under ruling (y).
use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
struct RawOracle<'a,const N:usize,const C:usize>{
 bytes:&'a[u8],at:usize,replies:[[u8;N];C],posts:[usize;C],calls:usize,
 seen:[usize;C],ptrs:[*const u8;C],lens:[usize;C],frame:[u8;C],observe:usize,
}
impl<const N:usize,const C:usize> RawOracle<'_,N,C>{
 fn raw(&mut self)->[u8;N]{
  let i=self.calls;assert!(i<C);self.calls+=1;
  self.seen[i]=self.at;self.ptrs[i]=self.bytes.as_ptr();self.lens[i]=self.bytes.len();
  self.frame[i]=self.bytes[self.observe];self.at=self.posts[i];self.replies[i]
 }
}
// Each query chunk is a literal contiguous subsequence of resume's initializer.
fn query8(r:&mut RawOracle<4,8>)->[u32;8]{[
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw()),
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw()),
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw()),
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw())]}
fn query6(r:&mut RawOracle<4,6>)->[u32;6]{[
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw()),
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw()),
 u32::from_le_bytes(r.raw()),u32::from_le_bytes(r.raw())]}
fn raw_pre<const N:usize,const C:usize>(bytes:&[u8;1768])->RawOracle<'_,N,C>{
 let observe:usize=kani::any();kani::assume(observe<1768);
 RawOracle{bytes,at:kani::any(),replies:kani::any(),posts:kani::any(),calls:0,
 seen:[0;C],ptrs:[core::ptr::null();C],lens:[0;C],frame:[0;C],observe}
}
fn frame<const N:usize,const C:usize>(r:&RawOracle<N,C>,start:usize,bytes:&[u8;1768]){
 assert_eq!(r.calls,C);assert_eq!(r.at,r.posts[C-1]);
 let j:usize=kani::any();kani::assume(j<C);
 let expect=if j==0{start}else{r.posts[j-1]};
 assert_eq!(r.seen[j],expect^(if cfg!(NKK_bad_backing){1}else{0}));
 assert_eq!(r.ptrs[j],bytes.as_ptr());assert_eq!(r.lens[j],1768);
 assert_eq!(r.frame[j],bytes[r.observe]);assert_eq!(r.bytes[r.observe],bytes[r.observe]);
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn query_chunk8(){
 let bytes:[u8;1768]=kani::any();let mut r=raw_pre::<4,8>(&bytes);let start=r.at;
 let out=query8(&mut r);frame(&r,start,&bytes);
 let j:usize=kani::any();kani::assume(j<8);
 assert_eq!(out[j],u32::from_le_bytes(r.replies[j])^(if cfg!(NKK_invert){1}else{0}));
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn query_chunk6(){
 let bytes:[u8;1768]=kani::any();let mut r=raw_pre::<4,6>(&bytes);let start=r.at;
 let out=query6(&mut r);frame(&r,start,&bytes);
 let j:usize=kani::any();kani::assume(j<6);
 assert_eq!(out[j],u32::from_le_bytes(r.replies[j])^(if cfg!(NKK_invert){1}else{0}));
}
// Literal state/root segment of resume, with exact source evaluation order.
fn roots(r:&mut RawOracle<32,3>)->([u8;32],[[u8;32];2]){
 let state=r.raw();let roots=[r.raw(),r.raw()];(state,roots)
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn state_roots_stage(){
 let bytes:[u8;1768]=kani::any();let mut r=raw_pre::<32,3>(&bytes);let start=r.at;
 let (state,roots)=roots(&mut r);frame(&r,start,&bytes);
 let j:usize=kani::any();kani::assume(j<32);
 assert_eq!(state[j],r.replies[0][j]^(if cfg!(NKK_invert){1}else{0}));
 assert_eq!(roots[0][j],r.replies[1][j]);assert_eq!(roots[1][j],r.replies[2][j]);
}
