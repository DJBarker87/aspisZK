use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn build(){let queries:[u32;22]=kani::any();let j:usize=kani::any();kani::assume(j<12);let tree:usize=kani::any();kani::assume(tree<3);let mut keys:[u64;16]=kani::any();let before=keys;
 let u=queries[10+j];let index=if tree==2{u/4}else{u};keys[j]=((index as u64)<<8)|(j as u64);
 let k:usize=kani::any();kani::assume(k<16);if cfg!(NIL_invert){keys[k]^=1;}assert_eq!(keys[k],if k==j{(index as u64)*256+j as u64}else{before[k]});}
fn sort(){let mut keys:[u64;16]=kani::any();let before=keys;let mut j:usize=kani::any();kani::assume(j<12);let old=j;
 let more=j>0&&batch_key_at(&keys,j-1)>batch_key_at(&keys,j);
 if j>0&&batch_key_at(&keys,j-1)>batch_key_at(&keys,j){keys.swap(j-1,j);j-=1;}
 let k:usize=kani::any();kani::assume(k<16);if cfg!(NIL_invert){keys[k]^=1;}
 assert_eq!(j,if more{old-1}else{old});assert_eq!(keys[k],if more&&k==old{before[old-1]}else if more&&k+1==old{before[old]}else{before[k]});}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u64]>::copy_from_slice,KMX_copy_from_slice)]
fn key_build(){build();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u64]>::copy_from_slice,KMX_copy_from_slice)]
fn key_build_renamed(){build();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u64]>::copy_from_slice,KMX_copy_from_slice)]
fn key_sort(){sort();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u64]>::copy_from_slice,KMX_copy_from_slice)]
fn key_sort_renamed(){sort();}
