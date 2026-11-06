use super::*;
use core::cell::RefCell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct Log {
 entered:bool,public_ptr:*const u8,public_len:usize,
 proof_ptr:*const u8,proof_len:usize,checkpoint_ptr:*const u8,checkpoint_len:usize,
 reply:Result<(),Error>,
}
#[derive(Clone,Copy)]
struct NLW_Hash<'a>(&'a RefCell<Log>);
impl aspis_core::Digest32 for NLW_Hash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(parts.len(),3);
  let tag:u8=kani::any();let reply=NLW_decode(tag);
  *self.0.borrow_mut()=Log{entered:true,public_ptr:parts[0].as_ptr(),public_len:parts[0].len(),proof_ptr:parts[1].as_ptr(),proof_len:parts[1].len(),checkpoint_ptr:parts[2].as_ptr(),checkpoint_len:parts[2].len(),reply};
  let mut out=[0;32];out[0]=tag;out
 }
}
fn NLW_parse_success(_proof:&[u8])->Result<Variant,Error>{Ok(Variant::S2)}
fn NLW_parse_error(_proof:&[u8])->Result<Variant,Error>{Err(Error::Parse)}
fn NLW_error()->Error {match kani::any::<u8>()%8 {0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
fn NLW_decode(tag:u8)->Result<(),Error> {match tag%9 {0=>Ok(()),1=>Err(Error::Parse),2=>Err(Error::Semantic),3=>Err(Error::Transcript),4=>Err(Error::Relation),5=>Err(Error::Merkle),6=>Err(Error::Query),7=>Err(Error::Checkpoint),_=>Err(Error::Allocation)}}
fn NLW_common<H:aspis_core::Digest32>(public:&[u8],proof:&[u8],checkpoint:&[u8],hash:H,_obs:Observer)->Result<(),Error>{
 NLW_decode(hash.digest(&[public,proof,checkpoint])[0])
}
fn NLW_parent<const INVERSE:bool,const SUCCESS:bool>() {
 // Fixed caller-established extents; contents are not read by these cuts.
 // Whole arbitrary-content coverage is a separate obligation, never inferred.
 let public=[0u8;1880];let proof=[0u8;57607];let checkpoint=[0u8;1768];
 let n:usize=kani::any();kani::assume(n<=1880);
 let p=&public[..n];
 let seed=Log{entered:false,public_ptr:core::ptr::null(),public_len:0,proof_ptr:core::ptr::null(),proof_len:0,checkpoint_ptr:core::ptr::null(),checkpoint_len:0,reply:Ok(())};
 let log=RefCell::new(seed);let hash=NLW_Hash(&log);
 let result=tx2_authenticated(p,&proof,&checkpoint,hash,None);
 let post=*log.borrow();
 let exact=if SUCCESS {
  post.entered&&post.public_ptr==p.as_ptr()&&post.public_len==p.len()&&post.proof_ptr==proof.as_ptr()&&post.proof_len==57607&&post.checkpoint_ptr==checkpoint.as_ptr()&&post.checkpoint_len==1768&&result==post.reply
 }else{!post.entered&&result==Err(Error::Parse)};
 assert!(exact!=INVERSE,"NLW actual auth call cut: exact forwarding or parser error prefix");
}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(parse_shape,NLW_parse_success)]
#[kani::stub(tx2_common::<NLW_Hash<'_>>,NLW_common)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_auth_success(){NLW_parent::<false,true>();}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(parse_shape,NLW_parse_success)]
#[kani::stub(tx2_common::<NLW_Hash<'_>>,NLW_common)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_auth_success_inverse(){NLW_parent::<true,true>();}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(parse_shape,NLW_parse_error)]
#[kani::stub(tx2_common::<NLW_Hash<'_>>,NLW_common)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_auth_error(){NLW_parent::<false,false>();}
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(parse_shape,NLW_parse_error)]
#[kani::stub(tx2_common::<NLW_Hash<'_>>,NLW_common)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_auth_error_inverse(){NLW_parent::<true,false>();}

// Source-ordered cut contracts. A parent carries all descriptor identities,
// borrow ledger identity, owned-buffer identity and allocator event cursor.
// Empty modifies is essential: identity fields alone do not prove payload frames.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct NLW_Parent {spans:[usize;6],hash:usize,descriptors:usize,loans:usize,owned:usize,allocator:usize,cursor:usize}
fn NLW_any_parent()->NLW_Parent {NLW_Parent{spans:kani::any(),hash:kani::any(),descriptors:kani::any(),loans:kani::any(),owned:kani::any(),allocator:kani::any(),cursor:kani::any()}}
fn NLW_parse_ref(s:NLW_Parent,r:Result<Variant,Error>)->Result<NLW_Parent,Error>{match r{Ok(_)=>Ok(s),Err(e)=>Err(e)}}
#[kani::modifies()]
#[kani::ensures(|out|*out==NLW_parse_ref(s,r))]
fn NLW_parse_segment(s:NLW_Parent,r:Result<Variant,Error>)->Result<NLW_Parent,Error>{r?;Ok(s)}
#[kani::modifies()]
#[kani::ensures(|out|*out!=NLW_parse_ref(s,r))]
fn NLW_parse_inverse_segment(s:NLW_Parent,r:Result<Variant,Error>)->Result<NLW_Parent,Error>{r?;Ok(s)}
fn NLW_any_parse()->Result<Variant,Error>{if kani::any(){Ok(Variant::S2)}else{Err(NLW_error())}}
#[kani::proof_for_contract(NLW_parse_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_parse_segment_contract(){NLW_parse_segment(NLW_any_parent(),NLW_any_parse());}
#[kani::proof_for_contract(NLW_parse_inverse_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_parse_segment_inverse(){NLW_parse_inverse_segment(NLW_any_parent(),NLW_any_parse());}
#[kani::modifies()]
#[kani::ensures(|out|*out==s)]
fn NLW_marker_segment(s:NLW_Parent)->NLW_Parent{mark(None,Phase::Parsed);s}
#[kani::modifies()]
#[kani::ensures(|out|*out!=s)]
fn NLW_marker_inverse_segment(s:NLW_Parent)->NLW_Parent{mark(None,Phase::Parsed);s}
#[kani::proof_for_contract(NLW_marker_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_marker_segment_contract(){NLW_marker_segment(NLW_any_parent());}
#[kani::proof_for_contract(NLW_marker_inverse_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_marker_segment_inverse(){NLW_marker_inverse_segment(NLW_any_parent());}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct NLW_Completed{post:NLW_Parent,reply:Result<(),Error>}
#[kani::modifies()]
#[kani::ensures(|out|out.post==post&&out.reply==reply)]
fn NLW_return_segment(post:NLW_Parent,reply:Result<(),Error>)->NLW_Completed{NLW_Completed{post,reply}}
#[kani::modifies()]
#[kani::ensures(|out|!(out.post==post&&out.reply==reply))]
fn NLW_return_inverse_segment(post:NLW_Parent,reply:Result<(),Error>)->NLW_Completed{NLW_Completed{post,reply}}
#[kani::proof_for_contract(NLW_return_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_return_segment_contract(){let r=if kani::any(){Ok(())}else{Err(NLW_error())};NLW_return_segment(NLW_any_parent(),r);}
#[kani::proof_for_contract(NLW_return_inverse_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_return_segment_inverse(){let r=if kani::any(){Ok(())}else{Err(NLW_error())};NLW_return_inverse_segment(NLW_any_parent(),r);}
// Local cfg(kani) generators enumerate every deployed enum arm.
impl kani::Arbitrary for Error {fn any()->Self{NLW_error()}}
impl kani::Arbitrary for NLW_Parent {fn any()->Self{NLW_any_parent()}}
impl kani::Arbitrary for NLW_Completed {fn any()->Self{Self{post:kani::any(),reply:kani::any()}}}

#[kani::modifies()]
#[kani::ensures(|out|out.is_ok())]
fn NLW_rp_weak(s:NLW_Parent)->Result<NLW_Parent,Error>{Ok(s)}
#[kani::modifies()]
#[kani::ensures(|out|!(out.is_ok()))]
fn NLW_rp_weak_inverse(s:NLW_Parent)->Result<NLW_Parent,Error>{Ok(s)}
#[kani::modifies()]
#[kani::ensures(|_out|true)]
fn NLW_rp_bad_modifies(s:NLW_Parent,external:&mut u8)->Result<NLW_Parent,Error>{*external=1;Ok(s)}
#[kani::proof_for_contract(NLW_rp_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_rp_weak_contract(){NLW_rp_weak(NLW_any_parent());}
#[kani::proof_for_contract(NLW_rp_weak_inverse)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_rp_weak_inverse_contract(){NLW_rp_weak_inverse(NLW_any_parent());}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_rp_real_assertion(){let s=NLW_any_parent();let out=NLW_rp_weak(s);assert_eq!(out,Ok(s));}
#[kani::proof]
#[kani::stub_verified(NLW_rp_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_rp_unimplied_assertion(){let s=NLW_any_parent();let out=NLW_rp_weak(s);assert_eq!(out,Ok(s));}
#[kani::proof_for_contract(NLW_rp_bad_modifies)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_rp_modifies_violation(){let mut external=0;NLW_rp_bad_modifies(NLW_any_parent(),&mut external);}

#[kani::modifies()]
#[kani::ensures(|out|out.spans[0]==s.spans[0])]
fn NLW_parent_weak(s:NLW_Parent)->NLW_Parent{s}
#[kani::modifies()]
#[kani::ensures(|out|!(out.spans[0]==s.spans[0]))]
fn NLW_parent_weak_inverse(s:NLW_Parent)->NLW_Parent{s}
#[kani::modifies()]
#[kani::ensures(|_out|true)]
fn NLW_parent_bad_modifies(s:NLW_Parent,external:&mut u8)->NLW_Parent{*external=1;s}
#[kani::proof_for_contract(NLW_parent_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_parent_weak_contract(){NLW_parent_weak(NLW_any_parent());}
#[kani::proof_for_contract(NLW_parent_weak_inverse)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_parent_weak_inverse_contract(){NLW_parent_weak_inverse(NLW_any_parent());}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_parent_real_assertion(){let s=NLW_any_parent();let out=NLW_parent_weak(s);assert_eq!(out,s);}
#[kani::proof]
#[kani::stub_verified(NLW_parent_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_parent_unimplied_assertion(){let s=NLW_any_parent();let out=NLW_parent_weak(s);assert_eq!(out,s);}
#[kani::proof_for_contract(NLW_parent_bad_modifies)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_parent_modifies_violation(){let mut external=0;NLW_parent_bad_modifies(NLW_any_parent(),&mut external);}

#[kani::modifies()]
#[kani::ensures(|out|out.reply==Ok(()))]
fn NLW_completed_weak(s:NLW_Parent)->NLW_Completed{NLW_Completed{post:s,reply:Ok(())}}
#[kani::modifies()]
#[kani::ensures(|out|!(out.reply==Ok(())))]
fn NLW_completed_weak_inverse(s:NLW_Parent)->NLW_Completed{NLW_Completed{post:s,reply:Ok(())}}
#[kani::modifies()]
#[kani::ensures(|_out|true)]
fn NLW_completed_bad_modifies(s:NLW_Parent,external:&mut u8)->NLW_Completed{*external=1;NLW_Completed{post:s,reply:Ok(())}}
#[kani::proof_for_contract(NLW_completed_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_completed_weak_contract(){NLW_completed_weak(NLW_any_parent());}
#[kani::proof_for_contract(NLW_completed_weak_inverse)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_completed_weak_inverse_contract(){NLW_completed_weak_inverse(NLW_any_parent());}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_completed_real_assertion(){let s=NLW_any_parent();let out=NLW_completed_weak(s);assert_eq!(out,NLW_Completed{post:s,reply:Ok(())});}
#[kani::proof]
#[kani::stub_verified(NLW_completed_weak)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_completed_unimplied_assertion(){let s=NLW_any_parent();let out=NLW_completed_weak(s);assert_eq!(out,NLW_Completed{post:s,reply:Ok(())});}
#[kani::proof_for_contract(NLW_completed_bad_modifies)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NLW_completed_modifies_violation(){let mut external=0;NLW_completed_bad_modifies(NLW_any_parent(),&mut external);}
