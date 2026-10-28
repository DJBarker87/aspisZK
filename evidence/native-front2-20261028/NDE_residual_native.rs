fn NDE_canon(q:QM31)->bool{q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff}
#[kani::proof] #[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::stub(QM31::mul,crate::NDE_field::qm31)]
fn NDE_residual_domain(){
 let v:[QM31;10]=kani::any();for q in v{kani::assume(NDE_canon(q));}
 let row=CopyRowExtension{producer_values:[v[0],v[1]],consumer_values:[v[2],v[3]],producer_weights:[v[4],v[5]],consumer_weights:[v[6],v[7]]};
 unsafe{crate::NDE_field::NDE_COUNT=0;}
 let out=super::copy_residual(row,v[8],v[9]);
 assert!((unsafe{crate::NDE_field::NDE_COUNT==9}&&NDE_canon(out))!=cfg!(NDE_domain_invert));
}
