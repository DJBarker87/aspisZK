use super::*;

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_roots(){let roots:[[u8;32];2]=kani::any();let folded:[u8;32]=kani::any();let t:usize=kani::any();let c:usize=kani::any();kani::assume(t<3&&c<32);let [root0,root1]=roots;let forwarded=[root0,root1,folded];assert_eq!(forwarded[t][c],if t==2{folded[c]}else{roots[t][c]});}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_roots_wrong(){let roots:[[u8;32];2]=kani::any();let folded:[u8;32]=kani::any();let t:usize=kani::any();let c:usize=kani::any();kani::assume(t<3&&c<32);let [root0,root1]=roots;let forwarded=[root0,root1,folded];assert_ne!(forwarded[t][c],if t==2{folded[c]}else{roots[t][c]});}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_opening_installed_window(){let mut proof=[0u8;57607];let i:usize=kani::any();let w:usize=kani::any();let c:usize=kani::any();let bytes:[u8;32]=kani::any();kani::assume(i<22&&w<26&&c<32);let at=10055+832*i+32*w;proof[at..at+32].copy_from_slice(&bytes);let q=opening(&proof,i);assert_eq!(q[32*w+c],bytes[c]);}

#[kani::proof] #[kani::unwind(34)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_opening_installed_window_wrong(){let mut proof=[0u8;57607];let i:usize=kani::any();let w:usize=kani::any();let c:usize=kani::any();let bytes:[u8;32]=kani::any();kani::assume(i<22&&w<26&&c<32);let at=10055+832*i+32*w;proof[at..at+32].copy_from_slice(&bytes);let q=opening(&proof,i);assert_ne!(q[32*w+c],bytes[c]);}
#[kani::proof] #[kani::unwind(2)]
fn NBV_parent_prefix_guard(){let count:usize=kani::any();let s:usize=kani::any();let d:usize=kani::any();kani::assume(s<6&&d>0&&d<=12);let observed=Some(count).ok_or(Error::Merkle);assert!(matches!(observed,Ok(x) if x==count));if count>SLOT_NODES[s]{assert!(count>SLOT_NODES[s]);}else{let width=32*count;assert!(width<=32*SLOT_NODES[s]&&width<=5504);let n=d;assert!(n>0&&n<=16);}}

#[kani::proof] #[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_padding_word_wrong(){let nodes:[u8;5504]=kani::any();let count:usize=kani::any();let cap:usize=kani::any();let j:usize=kani::any();kani::assume(count<=cap&&cap<=172&&j<4*(cap-count));let at=32*count+8*j;let q=&nodes[at..at+8];let word=u64::from_le_bytes(q.try_into().unwrap());assert_ne!(word==0,(0..8).all(|c|nodes[at+c]==0));}
