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
