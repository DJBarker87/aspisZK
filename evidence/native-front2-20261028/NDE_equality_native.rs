pub(super) static mut NDE_EQ_PRODUCT:QM31=QM31::ZERO;
pub(super) static mut NDE_EQ_INDEX:usize=1;
fn NDE_eq_canon(q:QM31)->bool{q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff}
#[kani::proof] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::NDE_field::qm31)]
fn NDE_equality_domain(){
 let left:[QM31;10]=kani::any();let right:[QM31;10]=kani::any();for q in left{kani::assume(NDE_eq_canon(q));}for q in right{kani::assume(NDE_eq_canon(q));}
 let product:QM31=kani::any();kani::assume(NDE_eq_canon(product));let index:usize=kani::any();kani::assume(index>=1&&index<=10);
 unsafe{NDE_EQ_PRODUCT=product;NDE_EQ_INDEX=index;crate::NDE_field::NDE_COUNT=0;}
 let out=super::equality_value(&left,&right);
 assert!((unsafe{crate::NDE_field::NDE_COUNT==if index<10{3}else{1}}&&NDE_eq_canon(out))!=cfg!(NDE_domain_invert));
}
