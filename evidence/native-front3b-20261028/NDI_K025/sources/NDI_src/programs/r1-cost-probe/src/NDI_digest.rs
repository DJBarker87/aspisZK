extern crate alloc;
use super::*;
#[path="NDI_reference.rs"] mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]
struct Script { mode:u8,call:u8,row:u8,state:*const [u8;32],absorbed:*const [u8;32],block:*const [u8;32],advanced:*const [u8;32],payload:*const u8,length:usize,root:*const u8 }
static mut SCRIPT:Script=Script{mode:0,call:0,row:0,state:core::ptr::null(),absorbed:core::ptr::null(),block:core::ptr::null(),advanced:core::ptr::null(),payload:core::ptr::null(),length:0,root:core::ptr::null()};
fn digest_reply(_: &SolanaDigest,parts:&[&[u8]])->[u8;32] {
 unsafe {
  let script=SCRIPT;
  SCRIPT.call+=1;
  if script.mode==0 {
   assert_eq!(script.call,0);assert_eq!(parts.len(),5);
   assert_eq!(parts[0],aspis_r1_cost_probe::r1_wire::DOMAIN);assert_eq!(parts[1],&[0]);
   assert_eq!(parts[2].len(),4);
   assert_eq!(u32::from_le_bytes(parts[2].try_into().unwrap()),script.length as u32);
   assert_eq!(parts[3].as_ptr(),script.payload);assert_eq!(parts[3].len(),script.length);
   assert_eq!(parts[4].as_ptr(),script.root);assert_eq!(parts[4].len(),32);
   *script.absorbed
  } else if script.call==0 {
   assert_eq!(parts.len(),3);assert_eq!(parts[0],&*script.state);
   assert_eq!(parts[1],&[0,0xa0+script.row]);
   assert_eq!(parts[2].as_ptr(),script.payload);assert_eq!(parts[2].len(),script.length);
   *script.absorbed
  } else if script.call==1 {
   assert_eq!(parts.len(),2);assert_eq!(parts[0],&*script.absorbed);assert_eq!(parts[1],&[1]);*script.block
  } else {
   assert_eq!(script.call,2);assert_eq!(parts.len(),2);assert_eq!(parts[0],&*script.absorbed);assert_eq!(parts[1],&[2]);*script.advanced
  }
 }
}
#[kani::requires(public.len()<=1880 && coordinate<32)]
#[kani::modifies(unsafe { &mut SCRIPT })]
#[kani::ensures(|r| (*r==reference::transcript_new_byte_ref(reply,coordinate)) != cfg!(NDI_invert_new))]
fn new_packet(public:&[u8],root:&[u8;32],reply:[u8;32],coordinate:usize)->(u8,u8,u8) {
 unsafe { SCRIPT=Script{mode:0,call:0,row:0,state:core::ptr::null(),absorbed:&reply,block:core::ptr::null(),advanced:core::ptr::null(),payload:public.as_ptr(),length:public.len(),root:root.as_ptr()}; }
 let (state,next)=aspis_r1_cost_probe::r1_wire::NDI_new_for_backend(SolanaDigest,public,root).unwrap();
 (state[coordinate],next,unsafe{SCRIPT.call})
}
#[kani::requires(row<=26 && framed.len()<=3717 && coordinate<32)]
#[kani::modifies(unsafe { &mut SCRIPT })]
#[kani::ensures(|r| (*r==reference::transcript_sample_byte_ref(block,advanced,row,coordinate)) != cfg!(NDI_invert_sample))]
fn sample_packet(state:*const [u8;32],absorbed:*const [u8;32],block:*const [u8;32],advanced:*const [u8;32],row:u8,framed:&[u8],coordinate:usize)->(u8,u8,u8,u8) {
 unsafe { SCRIPT=Script{mode:1,call:0,row,state:&state,absorbed:&absorbed,block:&block,advanced:&advanced,payload:framed.as_ptr(),length:framed.len(),root:core::ptr::null()}; }
 let (out,after,next)=aspis_r1_cost_probe::r1_wire::NDI_sample_for_backend(SolanaDigest,state,row,row,framed).unwrap();
 (out[coordinate],after[coordinate],next,unsafe{SCRIPT.call})
}
#[kani::proof_for_contract(new_packet)] #[kani::unwind(40)]
#[kani::stub(<SolanaDigest as aspis_core::Digest32>::digest,digest_reply)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn new_contract(){let public:[u8;1880]=kani::any();let n:usize=kani::any();kani::assume(n<=1880);let root:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<32);let _=new_packet(&public[..n],&root,kani::any(),j);}
#[kani::proof_for_contract(sample_packet)] #[kani::unwind(40)]
#[kani::stub(<SolanaDigest as aspis_core::Digest32>::digest,digest_reply)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn sample_contract(){let frame:[u8;3717]=kani::any();let n:usize=kani::any();kani::assume(n<=3717);let row:u8=kani::any();kani::assume(row<=26);let j:usize=kani::any();kani::assume(j<32);let _=sample_packet(kani::any(),kani::any(),kani::any(),kani::any(),row,&frame[..n],j);}
