use super::*;
#[path="NDN_reference.rs"] mod reference;
fn canon(q:QM31)->bool {q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff}
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
pub(super) static mut PRE:[QM31;7]=[QM31::ZERO;7];
pub(super) static mut BLOCK:usize=0;
pub(super) static mut AFTER:[QM31;7]=[QM31::ZERO;7];
pub(super) static mut NEXT:usize=0;
#[cfg(NDN_active_high)]
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn active_high_window(){
 let selectors=Selectors{high:kani::any(),low:kani::any()};
 let pre:[QM31;7]=kani::any();let block:usize=kani::any();let j:usize=kani::any();
 kani::assume(block<64&&j<7);
 let coordinate=reference::active_coordinate(constants::ACTIVE_ROW_MASKS[block]);
 kani::assume(canon(pre[coordinate])&&canon(selectors.high[block]));
 unsafe{PRE=pre;BLOCK=block;}
 let _=selectors.active_mask_basis();
 let expected=if j==coordinate{let a=words(pre[j]);let b=words(selectors.high[block]);core::array::from_fn(|i|reference::add_word(a[i],b[i]))}else{words(pre[j])};
 assert!((unsafe{words(AFTER[j])==expected&&NEXT==block+1}) != cfg!(NDN_invert));
}
