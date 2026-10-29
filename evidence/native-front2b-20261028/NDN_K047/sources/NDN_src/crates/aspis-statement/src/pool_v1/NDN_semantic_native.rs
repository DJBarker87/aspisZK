use super::*;
#[path="NDN_reference.rs"] mod reference;
fn canon(q:QM31)->bool {q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff}
fn words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
pub(super) static mut EQ_PRE:QM31=QM31::ZERO;
pub(super) static mut EQ_FACTOR:QM31=QM31::ZERO;
pub(super) static mut EQ_INDEX:usize=1;
pub(super) static mut EQ_ARGS:(QM31,QM31)=(QM31::ZERO,QM31::ZERO);
#[cfg(NDN_eq_factor)]
#[kani::proof] #[kani::unwind(12)]
#[kani::stub(QM31::mul,crate::NDE_field::qm31)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn equality_factor_window(){
 let a:QM31=kani::any();let b:QM31=kani::any();kani::assume(canon(a)&&canon(b));let j:usize=kani::any();kani::assume(j<4);
 unsafe{crate::NDE_field::NDE_COUNT=0;}
 let out=super::equality_value(&[a;10],&[b;10]);
 let aw=words(a);let bw=words(b);let pw=words(unsafe{crate::NDE_field::NDE_REPLY});let one=if j==0{1}else{0};
 let base=reference::sub_word(reference::sub_word(one,aw[j]),bw[j]);let expected=reference::factor_sum(base,pw[j]);
 let good=unsafe{crate::NDE_field::NDE_COUNT==1&&crate::NDE_field::NDE_LEFT==a&&crate::NDE_field::NDE_RIGHT==b}&&words(out)[j]==expected;
 assert!(good!=cfg!(NDN_invert));
}
#[cfg(NDN_eq_outer)]
#[kani::proof] #[kani::unwind(12)]
#[kani::stub(QM31::mul,crate::NDE_field::qm31)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn equality_outer_window(){
 let left:[QM31;10]=kani::any();let right:[QM31;10]=kani::any();let pre:QM31=kani::any();let factor:QM31=kani::any();kani::assume(canon(pre)&&canon(factor));
 let i:usize=kani::any();kani::assume(1<=i&&i<10);
 unsafe{EQ_PRE=pre;EQ_FACTOR=factor;EQ_INDEX=i;crate::NDE_field::NDE_COUNT=0;}
 let out=super::equality_value(&left,&right);
 let good=unsafe{crate::NDE_field::NDE_COUNT==1&&crate::NDE_field::NDE_LEFT==pre&&crate::NDE_field::NDE_RIGHT==factor&&out==crate::NDE_field::NDE_REPLY&&EQ_ARGS==(left[i],right[i])};
 assert!(good!=cfg!(NDN_invert));
}
pub(super) static mut FIELD_WORD:u32=0;
pub(super) static mut FIELD_BYTES:[u8;4]=[0;4];
pub(super) static mut FIELD_REACHED:bool=false;
pub(super) static mut FIELD_ERROR:bool=false;
#[cfg(NDN_fields_window)]
#[kani::proof] #[kani::unwind(16)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn fields_word_window(){
 use crate::pool_v1::{payment_relation::PoolV1PrivateTransferPublicV1,pair_tree_profile::{PoolV1PairLatePublicStatementV1,PoolV1PairLiveSnapshotV1},pair_terminal::PoolV1PairVerifiedAfterstateV1};
 let public=PoolV1PrivateTransferPublicV1{pool:[0;32],deployment_domain:[0;32],anchor_sequence:0,anchor_root:[M31::ZERO;8],nullifier:[M31::ZERO;8],asset_id:M31::ZERO,recipient_commitment:[M31::ZERO;8],change_commitment:[M31::ZERO;8]};
 let transition=PoolV1PairLatePublicStatementV1{live_snapshot:PoolV1PairLiveSnapshotV1{pool:[0;32],deployment_domain:[0;32],sequence:0,next_pair_index:0,current_root:[M31::ZERO;8],frontier:[[M31::ZERO;8];20]},candidate_afterstate:PoolV1PairVerifiedAfterstateV1{next_pair_index:0,next_root:[M31::ZERO;8],next_frontier:[[M31::ZERO;8];20]}};
 let word:u32=kani::any();let j:usize=kani::any();kani::assume(j<4);
 unsafe{FIELD_WORD=word;FIELD_REACHED=false;}
 let _=r0::Public::Transfer(&public,&transition).public_bytes();
 let good=if word<2147483647{unsafe{FIELD_REACHED&&!FIELD_ERROR&&FIELD_BYTES[j]==reference::field_byte(word,j)}}else{unsafe{!FIELD_REACHED&&FIELD_ERROR}};
 assert!(good!=cfg!(NDN_invert));
}
