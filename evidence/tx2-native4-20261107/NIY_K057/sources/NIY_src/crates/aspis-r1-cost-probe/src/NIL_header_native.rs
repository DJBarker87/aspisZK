use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
fn check(){let bytes:[u8;5]=kani::any();let i:usize=kani::any();kani::assume(i<=5);let mut it=bytes[i..].iter();let next=it.next();let mut cursor=i+(if next.is_some(){1}else{0});let answer=next.map(|&b|b!=0);if cfg!(NIL_invert){cursor^=1;}assert_eq!(cursor,if i<5{i+1}else{i});assert_eq!(it.len(),5-cursor);assert_eq!(answer,if i<5{Some(bytes[i]!=0)}else{None});}
#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn header_step(){check();}
#[kani::proof]
#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn header_step_renamed(){check();}
