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
pub(super) static mut COORD:usize=0;
pub(super) static mut LEFT:QM31=QM31::ZERO;
pub(super) static mut RIGHT:QM31=QM31::ZERO;
pub(super) static mut LOW_REPLY:QM31=QM31::ZERO;
#[cfg(NDN_active_route)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn active_route_window(){
 let selectors=Selectors{high:kani::any(),low:kani::any()};let pre:[QM31;7]=kani::any();let block:usize=kani::any();kani::assume(block<64);
 unsafe{PRE=pre;BLOCK=block;}
 let c=reference::active_coordinate(constants::ACTIVE_ROW_MASKS[block]);
 let _=selectors.active_mask_basis();
 assert!((unsafe{COORD==c&&LEFT==pre[c]&&RIGHT==selectors.high[block]})!=cfg!(NDN_invert));
}
#[cfg(NDN_active_sparse)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn active_add_window(){
 let a:QM31=kani::any();let b:QM31=kani::any();kani::assume(canon(a)&&canon(b));
 let selectors=Selectors{high:[b;64],low:[QM31::ZERO;16]};let block:usize=kani::any();let j:usize=kani::any();kani::assume(block<64&&j<7);
 unsafe{PRE=[a;7];BLOCK=block;}
 let c=reference::active_coordinate(constants::ACTIVE_ROW_MASKS[block]);let _=selectors.active_mask_basis();
 let aw=words(a);let bw=words(b);let expected=core::array::from_fn(|i|reference::active_high_word(aw[i],bw[i],j==c));
 assert!((unsafe{words(AFTER[j])==expected&&NEXT==block+1})!=cfg!(NDN_invert));
}
fn coordinate()->usize {if cfg!(NDN_coord0){0}else if cfg!(NDN_coord1){1}else if cfg!(NDN_coord2){2}else if cfg!(NDN_coord3){3}else if cfg!(NDN_coord4){4}else if cfg!(NDN_coord5){5}else{6}}
#[cfg(NDN_active_low)]
#[kani::proof] #[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn active_low_window(){
 let low:[QM31;16]=kani::any();for q in low {kani::assume(canon(q));}
 let selectors=Selectors{high:[QM31::ZERO;64],low};let c=coordinate();unsafe{COORD=c;}
 let mut expected=[0u32;4];let mut t=0usize;
 while t<reference::low_count(c){let w=words(low[reference::low_index(c,t)]);for i in 0..4 {expected[i]=reference::add_word(expected[i],w[i]);}t+=1;}
 let _=selectors.active_mask_basis();
 assert!((unsafe{words(LOW_REPLY)==expected})!=cfg!(NDN_invert));
}
