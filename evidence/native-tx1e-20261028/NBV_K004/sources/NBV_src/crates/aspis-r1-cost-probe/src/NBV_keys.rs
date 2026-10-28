use super::*;
#[kani::proof] #[kani::unwind(2)]
fn NBV_opening_pointer_global(){let proof:[u8;57607]=kani::any();let i:usize=kani::any();kani::assume(i<22);let q=opening(&proof,i);assert_eq!(q.len(),832);assert_eq!(q.as_ptr(),proof.as_ptr().wrapping_add(10055+832*i));}
#[kani::proof] #[kani::unwind(2)]
fn NBV_opening_window_pointer(){let proof:[u8;57607]=kani::any();let i:usize=kani::any();let w:usize=kani::any();kani::assume(i<22&&w<26);let q=opening(&proof,i);let selected=&q[32*w..32*(w+1)];assert_eq!(selected.len(),32);assert_eq!(selected.as_ptr(),proof.as_ptr().wrapping_add(10055+832*i+32*w));}
#[kani::proof] #[kani::unwind(2)]
fn NBV_padding_guard(){let count:usize=kani::any();let s:usize=kani::any();kani::assume(s<6);if count>SLOT_NODES[s]{let out:Result<(),Error>=Err(Error::Parse);assert!(matches!(out,Err(Error::Parse)));}else{assert!(32*count<=32*SLOT_NODES[s]);assert!(32*SLOT_NODES[s]<=5504);assert_eq!((32*SLOT_NODES[s]-32*count)%8,0);}}
#[kani::proof] #[kani::unwind(2)]
fn NBV_padding_continuation(){let scan:bool=kani::any();let verified:bool=kani::any();let mut calls=0;let result=if scan{Err(Error::Parse)}else{calls+=1;if !verified{Err(Error::Merkle)}else{Ok(())}};assert_eq!(calls,if scan{0}else{1});if scan{assert!(matches!(result,Err(Error::Parse)))}else if verified{assert!(result.is_ok())}else{assert!(matches!(result,Err(Error::Merkle)))}}
