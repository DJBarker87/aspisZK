use super::*;
use core::cell::RefCell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// Returning-arm experiment only. This local log is NOT the full NLT footprint.
#[derive(Clone,Copy)]
struct NMK_Log { entered:bool, pub_ptr:*const u8, pub_len:usize, proof_ptr:*const u8,
 proof_len:usize, ck_ptr:*const u8, ck_len:usize, reply:u8, footprint:[u64;4], omit:bool, coverage:u8 }
#[derive(Clone,Copy)]
struct NMK_Hash<'a>(&'a RefCell<NMK_Log>);
impl aspis_core::Digest32 for NMK_Hash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(parts.len(),3);
  let reply:u8=kani::any();kani::assume(reply<9);
  let prior=*self.0.borrow();
  let mut footprint:[u64;4]=kani::any();
  let coverage=if prior.omit {footprint[3]=prior.footprint[3];7}else{15};
  *self.0.borrow_mut()=NMK_Log {entered:true,pub_ptr:parts[0].as_ptr(),pub_len:parts[0].len(),
   proof_ptr:parts[1].as_ptr(),proof_len:parts[1].len(),ck_ptr:parts[2].as_ptr(),ck_len:parts[2].len(),
   reply,footprint,omit:prior.omit,coverage};
  let mut out=[0;32];out[0]=reply;out
 }
}
fn NMK_reply(t:u8)->Result<(),Error>{match t {0=>Ok(()),1=>Err(Error::Parse),2=>Err(Error::Semantic),
 3=>Err(Error::Transcript),4=>Err(Error::Relation),5=>Err(Error::Merkle),6=>Err(Error::Query),
 7=>Err(Error::Checkpoint),_=>Err(Error::Allocation)}}
fn NMK_header(p:&[u8])->bool {
 p.len()==57607 && p[0]==compact::MAGIC[0] && p[1]==compact::MAGIC[1] && p[2]==compact::MAGIC[2] && p[3]==compact::MAGIC[3] && p[4]==compact::MAGIC[4] && p[5]==compact::MAGIC[5] && p[6]==compact::MAGIC[6] && p[7]==compact::MAGIC[7] && p[8]==2 && p[9]==0 && p[10]==0 && p[11]==0 && p[12]==0 && p[13]==0 && p[14]==0 && p[15]==0
}
fn NMK_parse_cut(p:&[u8])->Result<Variant,Error>{
 // CLOSED NLE_ParseInstall packet's complete returning law, no buffer writes.
 if NMK_header(p){Ok(Variant::S2)}else{Err(Error::Parse)}
}
fn NMK_marker_cut(_obs:Observer,_phase:Phase){}
fn NMK_common_cut<H:aspis_core::Digest32>(public:&[u8],proof:&[u8],checkpoint:&[u8],hash:H,_obs:Observer)->Result<(),Error>{
 assert_eq!(proof.len(),57607,"common own extent");assert!(public.len()<=1880,"common own public extent");
 // Root0 and the full NLT packet are NOT represented by this experimental cut.
 NMK_reply(hash.digest(&[public,proof,checkpoint])[0])
}
fn NMK_common_perturbed<H:aspis_core::Digest32>(public:&[u8],proof:&[u8],checkpoint:&[u8],hash:H,_obs:Observer)->Result<(),Error>{
 let tag=hash.digest(&[public,proof,checkpoint])[0];NMK_reply((tag+1)%9)
}
#[repr(C)]
struct NMK_Proof { header:[u8;16], suffix:[u8;57591] }
fn NMK_parent<const OK:bool,const SWAP:bool,const OMIT:bool>(){
 let public:[u8;1880]=kani::any();let storage=NMK_Proof{header:kani::any(),suffix:kani::any()};
 let proof=unsafe{core::slice::from_raw_parts((&storage as *const NMK_Proof).cast::<u8>(),57607)};let ck:[u8;1768]=kani::any();
 let n:usize=kani::any();kani::assume(n<=1880);let pub_= &public[..n];
 kani::assume(NMK_header(&proof)==OK);
 let seed=NMK_Log{entered:false,pub_ptr:core::ptr::null(),pub_len:0,proof_ptr:core::ptr::null(),proof_len:0,
  ck_ptr:core::ptr::null(),ck_len:0,reply:kani::any(),footprint:kani::any(),omit:OMIT,coverage:0};
 let log=RefCell::new(seed);let hash=NMK_Hash(&log);
 let result=if SWAP{tx2_authenticated(pub_,&ck,&proof,hash,None)}else{tx2_authenticated(pub_,&proof,&ck,hash,None)};
 let post=*log.borrow();
 if OK {
  assert!(post.entered);assert!(post.pub_ptr==pub_.as_ptr()&&post.pub_len==pub_.len());
  assert!(post.proof_ptr==proof.as_ptr()&&post.proof_len==proof.len());
  assert!(post.ck_ptr==ck.as_ptr()&&post.ck_len==ck.len());assert_eq!(result,NMK_reply(post.reply));
  assert_eq!(post.coverage,15,"independent coverage of four declared local cells");
 } else {assert!(!post.entered);assert_eq!(result,Err(Error::Parse));assert_eq!(post.footprint[0],seed.footprint[0]);assert_eq!(post.footprint[1],seed.footprint[1]);assert_eq!(post.footprint[2],seed.footprint[2]);assert_eq!(post.footprint[3],seed.footprint[3]);}

}
#[kani::proof]#[kani::unwind(17)]
#[kani::stub(parse_shape,NMK_parse_cut)]#[kani::stub(mark,NMK_marker_cut)]
#[kani::stub(tx2_common::<NMK_Hash<'_>>,NMK_common_cut)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMK_auth_return(){NMK_parent::<true,false,false>();}
#[kani::proof]#[kani::unwind(17)]
#[kani::stub(parse_shape,NMK_parse_cut)]#[kani::stub(mark,NMK_marker_cut)]
#[kani::stub(tx2_common::<NMK_Hash<'_>>,NMK_common_cut)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMK_auth_reject(){NMK_parent::<false,false,false>();}
#[kani::proof]#[kani::unwind(17)]
#[kani::stub(parse_shape,NMK_parse_cut)]#[kani::stub(mark,NMK_marker_cut)]
#[kani::stub(tx2_common::<NMK_Hash<'_>>,NMK_common_perturbed)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMK_auth_perturbed(){NMK_parent::<true,false,false>();}
#[kani::proof]#[kani::unwind(17)]
#[kani::stub(parse_shape,NMK_parse_cut)]#[kani::stub(mark,NMK_marker_cut)]
#[kani::stub(tx2_common::<NMK_Hash<'_>>,NMK_common_cut)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMK_auth_argument_mutant(){NMK_parent::<true,true,false>();}
#[kani::proof]#[kani::unwind(17)]
#[kani::stub(parse_shape,NMK_parse_cut)]#[kani::stub(mark,NMK_marker_cut)]
#[kani::stub(tx2_common::<NMK_Hash<'_>>,NMK_common_cut)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMK_auth_omitted_location(){NMK_parent::<true,false,true>();}
#[kani::proof]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMK_copy_negative(){let a:[u8;4]=kani::any();let mut b=[0;4];b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<4);assert_ne!(a[i],b[i]);}
