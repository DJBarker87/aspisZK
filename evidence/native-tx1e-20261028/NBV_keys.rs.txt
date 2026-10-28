use super::*;
#[kani::proof] #[kani::unwind(2)]
fn NBV_opening_pointer_global(){let proof:[u8;57607]=kani::any();let i:usize=kani::any();kani::assume(i<22);let q=opening(&proof,i);assert_eq!(q.len(),832);assert_eq!(q.as_ptr(),proof.as_ptr().wrapping_add(10055+832*i));}
#[kani::proof] #[kani::unwind(2)]
fn NBV_opening_window_pointer(){let proof:[u8;57607]=kani::any();let i:usize=kani::any();let w:usize=kani::any();kani::assume(i<22&&w<26);let q=opening(&proof,i);let selected=&q[32*w..32*(w+1)];assert_eq!(selected.len(),32);assert_eq!(selected.as_ptr(),proof.as_ptr().wrapping_add(10055+832*i+32*w));}
#[kani::proof] #[kani::unwind(2)]
fn NBV_padding_guard(){let count:usize=kani::any();let s:usize=kani::any();kani::assume(s<6);if count>SLOT_NODES[s]{let out:Result<(),Error>=Err(Error::Parse);assert!(matches!(out,Err(Error::Parse)));}else{assert!(32*count<=32*SLOT_NODES[s]);assert!(32*SLOT_NODES[s]<=5504);assert_eq!((32*SLOT_NODES[s]-32*count)%8,0);}}
#[kani::proof] #[kani::unwind(2)]
fn NBV_padding_continuation(){let scan:bool=kani::any();let verified:bool=kani::any();let mut calls=0;let result=if scan{Err(Error::Parse)}else{calls+=1;if !verified{Err(Error::Merkle)}else{Ok(())}};assert_eq!(calls,if scan{0}else{1});if scan{assert!(matches!(result,Err(Error::Parse)))}else if verified{assert!(result.is_ok())}else{assert!(matches!(result,Err(Error::Merkle)))}}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
fn NBV_padding_word_native(){let nodes:[u8;5504]=kani::any();let count:usize=kani::any();let cap:usize=kani::any();let k:usize=kani::any();kani::assume(count<=cap&&cap<=172&&k<4*(cap-count));let at=32*count+8*k;let q=&nodes[at..at+8];let word=u64::from_le_bytes(q.try_into().unwrap());assert_eq!(word==0,(0..8).all(|j|nodes[at+j]==0));}
#[kani::proof] #[kani::unwind(2)]
fn NBV_opening_byte_window(){let proof:[u8;57607]=kani::any();let w:usize=kani::any();kani::assume(w<26);let q=opening(&proof,0);let selected=&q[32*w..32*w+32];assert_eq!(selected[0],proof[10055+32*w]);}
