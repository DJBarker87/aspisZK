extern crate alloc;
use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[path="PCG_pack_reference.rs"] mod reference;
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn word_association(){let digest:[u8;32]=kani::any();let chunk:usize=kani::any();let byte:usize=kani::any();let word:u64=kani::any();kani::assume(chunk<4&&byte<7);kani::assume(word<(1u64<<(8*byte)));let actual=(word<<8)|u64::from(digest[7*chunk+byte]);let expected=reference::word_step(word,digest[7*chunk+byte]);assert!((actual==expected)!=cfg!(PCG_NEG_PACK));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn write_window(){let mut seed:[u8;32]=kani::any();let chunk:usize=kani::any();let group:usize=kani::any();let other:usize=kani::any();let word:u64=kani::any();kani::assume(chunk<4&&group<8&&other<32);let old=seed[other];let offset=8*chunk+group;seed[offset]=((word>>(7*(7-group)))&0x7f)as u8;assert_eq!(seed[offset],((word>>(49-7*group))&127)as u8);if other!=offset{assert_eq!(seed[other],old);}assert!((seed[offset]<128)!=cfg!(PCG_NEG_PACK));}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn group_association(){let word:u64=kani::any();let group:usize=kani::any();kani::assume(group<8);let actual=((word>>(7*(7-group)))&0x7f)as u8;let expected=reference::group(word,group);assert!((actual==expected)!=cfg!(PCG_NEG_PACK));}
