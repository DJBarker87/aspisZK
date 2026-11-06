use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
// Pending occupied-arm frame, at the actual frozen child boundary; no reply.
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::unwind(40)]
fn NJV_pending_occupied() {
 let mut idx:[u32;16]=kani::any();let val:[[u8;32];16]=kani::any();
 let n:usize=kani::any();let i:usize=kani::any();let w:usize=kani::any();let at:usize=kani::any();let k:usize=kani::any();let j:usize=kani::any();
 kani::assume(0<n&&n<=16&&i+1<n&&w<=i&&at<=9216&&k<16&&j<32);
 kani::assume(idx[i+1]==idx[i]^1);
 let before_idx=idx[k];let before_val=val[k][j];let before_at=at;
 let parent=super::index_at(&idx,i)>>super::Arity::Two.bits();
 // Stop immediately BEFORE occupied_binary_parent(hash,val,i).
 let first=&val[i];let second=&val[i+1];
 if cfg!(NJV_bad_argument){idx[k]^=1;}
 assert_eq!(idx[k],before_idx);assert_eq!(val[k][j],before_val);assert_eq!(at,before_at);
 assert_eq!(parent,(idx[i] as u64/2)as u32);
 assert_eq!(first.as_ptr(),val[i].as_ptr());assert_eq!(second.as_ptr(),val[i+1].as_ptr());
 assert_eq!(first[j],val[i][j]);assert_eq!(second[j],val[i+1][j]);
}
