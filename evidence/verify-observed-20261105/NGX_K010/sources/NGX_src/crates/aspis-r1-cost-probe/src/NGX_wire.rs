use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct Hash(u64);
impl aspis_core::Digest32 for Hash { fn digest(&self,_parts:&[&[u8]])->[u8;32] { panic!("state accessor must not hash") } }
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn state_value() {
 let state:[u8;32]=kani::any(); let hash:u64=kani::any(); let next:u8=kani::any();
 let t=SemanticTranscript{state,hash:Hash(hash),next_row:next};
 let out=t.state();let i:usize=kani::any();kani::assume(i<32);
 assert!((out[i]==state[i])!=cfg!(NGX_invert));
 assert_eq!(t.state[i],state[i]);assert_eq!(t.hash.0,hash);assert_eq!(t.next_row,next);
}

struct Oracle { calls:usize, row:u8, initial:[u8;32], replies:[[u8;32];3], payload:*const u8, length:usize }
#[derive(Clone,Copy)]
struct OracleHash<'a>(&'a core::cell::RefCell<Oracle>);
impl aspis_core::Digest32 for OracleHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let mut o=self.0.borrow_mut();let n=o.calls;assert!(n<3);
  if n==0 {
   assert_eq!(parts.len(),3);assert_eq!(parts[0],&o.initial);
   assert_eq!(parts[1],&[0,160+o.row]);assert_eq!(parts[2].as_ptr(),o.payload);assert_eq!(parts[2].len(),o.length);
  } else {
   assert_eq!(parts.len(),2);assert_eq!(parts[0],&o.replies[0]);assert_eq!(parts[1],&[n as u8]);
  }
  o.calls+=1;o.replies[n]
 }
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn sample_value() {
 let state:[u8;32]=kani::any();let replies:[[u8;32];3]=kani::any();let row:u8=kani::any();kani::assume(row<=26);
 let next:u8=kani::any();let length:usize=kani::any();kani::assume(length<=3717);
 let mut payload=alloc::vec![0u8;length];let k:usize=kani::any();
 if length>0 {kani::assume(k<length);payload[k]=kani::any();}
 let oldbyte=if length>0 {payload[k]}else{0};
 let local=core::cell::RefCell::new(Oracle{calls:0,row,initial:state,replies,payload:payload.as_ptr(),length});
 let mut t=SemanticTranscript{state,hash:OracleHash(&local),next_row:next};
 let out=t.sample_block_validated(row,&payload);
 let i:usize=kani::any();kani::assume(i<32);
 if row!=next {assert!(matches!(out,Err(Error::RowOrder{expected,actual}) if expected==next&&actual==row));assert_eq!(local.borrow().calls,0);assert_eq!(t.state[i],state[i]);assert_eq!(t.next_row,next);}
 else {let out=out.unwrap();assert!((out[i]==replies[1][i])!=cfg!(NGX_invert));assert_eq!(t.state[i],replies[2][i]);assert_eq!(t.next_row,row+1);assert_eq!(local.borrow().calls,3);}
 assert!(core::ptr::eq(t.hash.0,&local));if length>0 {assert_eq!(payload[k],oldbyte);}
}

struct NewOracle { calls:usize, root:[u8;32],reply:[u8;32],payload:*const u8,length:usize }
#[derive(Clone,Copy)] struct NewHash<'a>(&'a core::cell::RefCell<NewOracle>);
impl aspis_core::Digest32 for NewHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let mut o=self.0.borrow_mut();assert_eq!(o.calls,0);assert_eq!(parts.len(),5);
  assert_eq!(parts[0],DOMAIN);assert_eq!(parts[1],&[0]);
  assert_eq!(parts[2],&(o.length as u32).to_le_bytes());
  assert_eq!(parts[3].as_ptr(),o.payload);assert_eq!(parts[3].len(),o.length);
  assert_eq!(parts[4],&o.root);o.calls+=1;o.reply
 }
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn new_value() {
 let root:[u8;32]=kani::any();let reply:[u8;32]=kani::any();let length:usize=kani::any();kani::assume(length<=57607);
 let mut public=alloc::vec![0u8;length];let k:usize=kani::any();if length>0 {kani::assume(k<length);public[k]=kani::any();}let oldbyte=if length>0 {public[k]}else{0};
 let local=core::cell::RefCell::new(NewOracle{calls:0,root,reply,payload:public.as_ptr(),length});
 let out=SemanticTranscript::new(NewHash(&local),&public,&root).unwrap();let i:usize=kani::any();kani::assume(i<32);
 assert!((out.state[i]==reply[i])!=cfg!(NGX_invert));assert_eq!(out.next_row,0);assert!(core::ptr::eq(out.hash.0,&local));assert_eq!(local.borrow().calls,1);if length>0 {assert_eq!(public[k],oldbyte);}
}
// Exact first stage of frozen new, lifted to an arbitrary length to cover the
// otherwise physically unallocatable >u32 rejection. No byte is fabricated.
fn new_length(length:usize)->Result<u32,Error> {let length=u32::try_from(length).map_err(|_|Error::Public)?;Ok(length)}
#[kani::proof]
fn new_length_value() {
 let length:usize=kani::any();let got=new_length(length);
 if length>u32::MAX as usize {assert!((matches!(got,Err(Error::Public)))!=cfg!(NGX_invert));}
 else {assert!((got==Ok(length as u32))!=cfg!(NGX_invert));}
}
