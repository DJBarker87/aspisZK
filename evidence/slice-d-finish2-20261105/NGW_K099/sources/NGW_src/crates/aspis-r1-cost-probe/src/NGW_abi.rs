use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
mod reference{include!("NGW_dot_reference.rs");}
#[kani::proof]#[kani::unwind(65)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn nine_word_model(){let w:[u64;9]=kani::any();kani::assume(w[8]<=64);let actual=NGM_helpers::make(w);let expected=reference::pack(reference::unpack(w));let j:usize=kani::any();kani::assume(j<9);let mut observed=if j<4{canonical::NGW_abi_canonical::word(&actual.c0,j)}else if j<8{canonical::NGW_abi_canonical::word(&actual.c1,j-4)}else{actual.count as u64};if cfg!(NGW_invert){observed^=1;}assert!(observed==expected[j]);}
