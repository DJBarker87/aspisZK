// Method control only: this minimal callee has no allocator/SDK footprint.
// It is not tx2_common or a replacement certificate for NLT_CompleteRoot.
use super::*;
use core::cell::Cell;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct NMD_Record {entered:bool,spans:[usize;6],reply:u8,effect:[u64;4]}
impl kani::Arbitrary for NMD_Record {fn any()->Self{Self{entered:kani::any(),spans:kani::any(),reply:kani::any(),effect:kani::any()}}}
impl kani::Arbitrary for Error {fn any()->Self{match kani::any::<u8>()%8 {0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}}
#[derive(Clone,Copy)]
struct NMD_Hash<'a>(&'a Cell<NMD_Record>);
fn NMD_decode(tag:u8)->Result<(),Error>{match tag%9{0=>Ok(()),1=>Err(Error::Parse),2=>Err(Error::Semantic),3=>Err(Error::Transcript),4=>Err(Error::Relation),5=>Err(Error::Merkle),6=>Err(Error::Query),7=>Err(Error::Checkpoint),_=>Err(Error::Allocation)}}
fn NMD_spans(p:&[u8],q:&[u8],c:&[u8])->[usize;6]{[p.as_ptr() as usize,p.len(),q.as_ptr() as usize,q.len(),c.as_ptr() as usize,c.len()]}
impl aspis_core::Digest32 for NMD_Hash<'_>{fn digest(&self,parts:&[&[u8]])->[u8;32]{assert_eq!(parts.len(),3);let mut r:NMD_Record=kani::any();r.entered=true;r.spans=NMD_spans(parts[0],parts[1],parts[2]);self.0.set(r);let mut out:[u8;32]=kani::any();out[0]=r.reply;out}}
fn NMD_child<H:aspis_core::Digest32>(p:&[u8],q:&[u8],c:&[u8],h:H,_obs:Observer)->Result<(),Error>{NMD_decode(h.digest(&[p,q,c])[0])}
fn NMD_law(p:&[u8],q:&[u8],c:&[u8],h:NMD_Hash<'_>,out:Result<(),Error>)->bool{let r=h.0.get();r.entered&&r.spans==NMD_spans(p,q,c)&&out==NMD_decode(r.reply)}
// T preserves the original callee's generic arity for this concrete H instance.
// No other H instantiation is claimed.
#[kani::requires(p.len()<=1880&&q.len()==57607&&c.len()==1768)]
#[kani::modifies(h.0.as_ptr())]
#[kani::ensures(|out|NMD_law(p,q,c,h,*out))]
fn NMD_wrapper<T:aspis_core::Digest32>(p:&[u8],q:&[u8],c:&[u8],h:NMD_Hash<'_>,obs:Observer)->Result<(),Error>{NMD_child(p,q,c,h,obs)}
#[kani::modifies(h.0.as_ptr())]
#[kani::ensures(|out|!NMD_law(p,q,c,h,*out))]
fn NMD_inverse_wrapper<T:aspis_core::Digest32>(p:&[u8],q:&[u8],c:&[u8],h:NMD_Hash<'_>,obs:Observer)->Result<(),Error>{NMD_child(p,q,c,h,obs)}
#[kani::modifies(h.0.as_ptr())]#[kani::ensures(|_out|true)]
fn NMD_weak<T:aspis_core::Digest32>(p:&[u8],q:&[u8],c:&[u8],h:NMD_Hash<'_>,obs:Observer)->Result<(),Error>{NMD_child(p,q,c,h,obs)}
#[kani::modifies(h.0.as_ptr())]#[kani::ensures(|_out|false)]
fn NMD_inverse_weak<T:aspis_core::Digest32>(p:&[u8],q:&[u8],c:&[u8],h:NMD_Hash<'_>,obs:Observer)->Result<(),Error>{NMD_child(p,q,c,h,obs)}
#[kani::modifies()]#[kani::ensures(|out|NMD_law(p,q,c,h,*out))]
fn NMD_bad_frame<T:aspis_core::Digest32>(p:&[u8],q:&[u8],c:&[u8],h:NMD_Hash<'_>,obs:Observer)->Result<(),Error>{NMD_child(p,q,c,h,obs)}
macro_rules! NMD_inputs {()=>{}} // inputs below are constructed locally in each harness.
#[kani::proof_for_contract(NMD_wrapper::<NMD_Hash<'_>>)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_record_contract(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);NMD_wrapper::<NMD_Hash<'_>>(&p,&q,&c,h,None);}
#[kani::proof_for_contract(NMD_inverse_wrapper::<NMD_Hash<'_>>)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_record_inverse(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);NMD_inverse_wrapper::<NMD_Hash<'_>>(&p,&q,&c,h,None);}
#[kani::proof_for_contract(NMD_weak::<NMD_Hash<'_>>)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_record_weak_contract(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);NMD_weak::<NMD_Hash<'_>>(&p,&q,&c,h,None);}
#[kani::proof_for_contract(NMD_inverse_weak::<NMD_Hash<'_>>)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_record_weak_inverse(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);NMD_inverse_weak::<NMD_Hash<'_>>(&p,&q,&c,h,None);}
#[kani::proof_for_contract(NMD_bad_frame::<NMD_Hash<'_>>)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_record_modifies(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);NMD_bad_frame::<NMD_Hash<'_>>(&p,&q,&c,h,None);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]

fn NMD_record_real(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);let out=NMD_weak::<NMD_Hash<'_>>(&p,&q,&c,h,None);assert!(NMD_law(&p,&q,&c,h,out));}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub_verified(NMD_weak::<NMD_Hash<'_>>)]
fn NMD_record_unimplied(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);let out=NMD_weak::<NMD_Hash<'_>>(&p,&q,&c,h,None);assert!(NMD_law(&p,&q,&c,h,out));}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(NMD_child::<NMD_Hash<'_>>,NMD_wrapper)]
#[kani::stub_verified(NMD_wrapper::<NMD_Hash<'_>>)]
fn NMD_record_parent(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);let out=NMD_child::<NMD_Hash<'_>>(&p,&q,&c,h,None);assert!(NMD_law(&p,&q,&c,h,out));}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(NMD_child::<NMD_Hash<'_>>,NMD_wrapper)]
#[kani::stub_verified(NMD_wrapper::<NMD_Hash<'_>>)]
fn NMD_record_parent_mutant(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);let out=NMD_child::<NMD_Hash<'_>>(&q,&p,&c,h,None);assert!(NMD_law(&p,&q,&c,h,out));}
#[kani::proof]#[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_copy_control(){let src:[u8;2]=kani::any();let mut dst=[0u8;2];dst.copy_from_slice(&src);assert!(dst[1]!=src[1]);}

fn NMD_generic_cut<H:aspis_core::Digest32>(p:&[u8],q:&[u8],c:&[u8],h:H,_obs:Observer)->Result<(),Error>{NMD_decode(h.digest(&[p,q,c])[0])}
#[kani::proof]
#[kani::stub(NMD_child::<NMD_Hash<'_>>,NMD_generic_cut)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_record_local_channel(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);let out=NMD_child(&p,&q,&c,h,None);assert!(NMD_law(&p,&q,&c,h,out));}
#[kani::proof]
#[kani::stub(NMD_child::<NMD_Hash<'_>>,NMD_generic_cut)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NMD_record_local_channel_mutant(){let p:[u8;1880]=kani::any();let q:[u8;57607]=kani::any();let c:[u8;1768]=kani::any();let state=Cell::new(kani::any::<NMD_Record>());let h=NMD_Hash(&state);let out=NMD_child(&q,&p,&c,h,None);assert!(NMD_law(&p,&q,&c,h,out));}
