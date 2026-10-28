use super::*;

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_posthash_decision(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let index:u32=kani::any();let mut d:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(d<=12&&k<16&&c<32);let old_d=d;let old_i=idx[k];let old_v=val[k][c];let result=if d>0&&same_batch_index(&idx,d-1,index){if !same_batch_leaf(&val,d-1,leaf){1u8}else{2u8}}else{0u8};assert_eq!(result,if d>0&&idx[d-1]==index{if val[d-1]!=leaf{1}else{2}}else{0});}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_posthash_decision_wrong(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let index:u32=kani::any();let mut d:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(d<=12&&k<16&&c<32);let old_d=d;let old_i=idx[k];let old_v=val[k][c];let result=if d>0&&same_batch_index(&idx,d-1,index){if !same_batch_leaf(&val,d-1,leaf){1u8}else{2u8}}else{0u8};assert_ne!(result,if d>0&&idx[d-1]==index{if val[d-1]!=leaf{1}else{2}}else{0});}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_posthash_new(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let index:u32=kani::any();let mut d:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(d<=12&&k<16&&c<32);let old_d=d;let old_i=idx[k];let old_v=val[k][c];kani::assume(d<12&&(d==0||idx[d-1]!=index));idx[d]=index;val[d]=leaf;d+=1;assert_eq!(d,old_d+1);assert_eq!(idx[k],if k==old_d{index}else{old_i});assert_eq!(val[k][c],if k==old_d{leaf[c]}else{old_v});}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_posthash_new_wrong(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let index:u32=kani::any();let mut d:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(d<=12&&k<16&&c<32);let old_d=d;let old_i=idx[k];let old_v=val[k][c];kani::assume(d<12&&(d==0||idx[d-1]!=index));idx[d]=index;val[d]=leaf;d+=1;assert_eq!(d,old_d+1);assert_eq!(idx[k],if k==old_d{index}else{old_i});assert_ne!(val[k][c],if k==old_d{leaf[c]}else{old_v});}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_posthash_equal(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let index:u32=kani::any();let mut d:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(d<=12&&k<16&&c<32);let old_d=d;let old_i=idx[k];let old_v=val[k][c];kani::assume(d>0&&idx[d-1]==index);kani::assume(val[d-1]==leaf);let result=if !same_batch_leaf(&val,d-1,leaf){Err(Error::Merkle)}else{Ok(())};assert_eq!(result.is_ok(),true);assert_eq!(d,old_d);assert_eq!(idx[k],old_i);assert_eq!(val[k][c],old_v);}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_posthash_equal_wrong(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let index:u32=kani::any();let mut d:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(d<=12&&k<16&&c<32);let old_d=d;let old_i=idx[k];let old_v=val[k][c];kani::assume(d>0&&idx[d-1]==index);kani::assume(val[d-1]==leaf);let result=if !same_batch_leaf(&val,d-1,leaf){Err(Error::Merkle)}else{Ok(())};assert_ne!(result.is_ok(),true);assert_eq!(d,old_d);assert_eq!(idx[k],old_i);assert_eq!(val[k][c],old_v);}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_posthash_unequal(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let index:u32=kani::any();let mut d:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(d<=12&&k<16&&c<32);let old_d=d;let old_i=idx[k];let old_v=val[k][c];kani::assume(d>0&&idx[d-1]==index);kani::assume(val[d-1]!=leaf);let result=if !same_batch_leaf(&val,d-1,leaf){Err(Error::Merkle)}else{Ok(())};assert_eq!(result.is_ok(),false);assert_eq!(d,old_d);assert_eq!(idx[k],old_i);assert_eq!(val[k][c],old_v);}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_posthash_unequal_wrong(){let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let leaf:[u8;32]=kani::any();let index:u32=kani::any();let mut d:usize=kani::any();let k:usize=kani::any();let c:usize=kani::any();kani::assume(d<=12&&k<16&&c<32);let old_d=d;let old_i=idx[k];let old_v=val[k][c];kani::assume(d>0&&idx[d-1]==index);kani::assume(val[d-1]!=leaf);let result=if !same_batch_leaf(&val,d-1,leaf){Err(Error::Merkle)}else{Ok(())};assert_ne!(result.is_ok(),false);assert_eq!(d,old_d);assert_eq!(idx[k],old_i);assert_eq!(val[k][c],old_v);}
#[kani::proof] #[kani::unwind(2)]
fn NBV_rebased_key_domain(){let queries:[u32;22]=kani::any();let batch:usize=kani::any();let j:usize=kani::any();let tree:usize=kani::any();kani::assume(batch<2&&tree<3);let (lo,n)=if batch==0{(0,10)}else{(10,12)};kani::assume(j<n);let u=queries[lo+j];kani::assume(u<262144);let index=if tree==2{u/4}else{u};let key=(u64::from(index)<<8)|j as u64;let selected=lo+(key&255)as usize;assert_eq!(selected,lo+j);assert!(selected<22);assert_eq!((key>>8)as u32,index);assert!(index<262144);if tree==2{assert!(index<65536);}}
#[kani::proof] #[kani::unwind(2)]
fn NBV_binary_arity(){assert_eq!(Arity::Two.bits(),1);assert_eq!(Arity::Two.width(),2);assert_eq!(Arity::Two.levels(),18);}
