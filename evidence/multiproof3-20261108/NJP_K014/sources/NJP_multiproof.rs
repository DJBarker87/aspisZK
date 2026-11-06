use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// Full caller bound: MAX_BATCH * LEAF_BITS * digest bytes = 9216.
// Every byte is arbitrary, including all coordinates outside the selected view.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn NJP_sibling_window() {
 let nodes:[u8;9216]=kani::any();let len:usize=kani::any();let at:usize=kani::any();let j:usize=kani::any();
 kani::assume(len<=9216&&at<=9216&&j<32);
 let part=nodes[..len].get(at..at+32);
 match part {
  Some(sibling)=>{
   assert!(at+32<=len);assert_eq!(sibling.len(),32);assert_eq!(sibling.as_ptr(),unsafe{nodes.as_ptr().add(at)});
   if cfg!(NJP_bad_argument){assert_eq!(sibling[j],nodes[at+j]^1)}else{assert_eq!(sibling[j],nodes[at+j])}
  },
  None=>{if cfg!(NJP_bad_argument){assert!(at+32<=len)}else{assert!(len<at+32)}}
 }
}
