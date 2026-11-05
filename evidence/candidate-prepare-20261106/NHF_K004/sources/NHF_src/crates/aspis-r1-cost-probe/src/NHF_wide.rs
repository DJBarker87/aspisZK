use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// No callee stub: the frozen byte parser executes on arbitrary bytes.
fn wide_result() {
 let proof:[u8;57607]=kani::any();
 let semantic:[u8;13831]=kani::any(); let y1:[u8;928]=kani::any();
 let slot:usize=kani::any();kani::assume(slot<8);
 let before:u8=kani::any();let unrelated=before;
 let out=wide_view(&proof,&semantic,&y1);
 let mut words=[0u32;8];let mut j=0;
 while j<8 {let at=7495+4*j;words[j]=u32::from_le_bytes([proof[at],proof[at+1],proof[at+2],proof[at+3]]);j+=1;}
 let canonical=words.iter().all(|x|*x<2147483647);
 let good=match out {
  Err(e)=>!canonical&&e==Error::Parse,
  Ok(v)=>{
   assert!(canonical);
   assert_eq!(v.inactive.to_limbs()[slot],words[slot]);
   assert!(v.variant==Variant::S2);
   assert!(core::ptr::eq(v.semantic.as_ptr(),semantic.as_ptr())&&v.semantic.len()==13831);
   assert!(core::ptr::eq(v.y1.as_ptr(),y1.as_ptr())&&v.y1.len()==928);
   assert!(core::ptr::eq(v.round0.as_ptr(),proof[7527..].as_ptr())&&v.round0.len()==224);
   assert!(core::ptr::eq(v.folded_root.unwrap().as_ptr(),proof[7751..].as_ptr()));
   assert!(core::ptr::eq(v.round1.as_ptr(),proof[7783..].as_ptr())&&v.round1.len()==224);
   assert!(core::ptr::eq(v.final_message.as_ptr(),proof[8007..].as_ptr())&&v.final_message.len()==2048);
   assert!(v.query_bytes.is_empty());true
  }
 };
 // This independent local is outside the modifies set.
 assert_eq!(unrelated,before);
 assert!(good != cfg!(NHF_invert));
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn wide_view_result(){wide_result()}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn wide_copy(){let a:[u8;32]=kani::any();let mut b:[u8;32]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<32);assert!((b[i]==a[i])!=cfg!(NHF_invert));}
