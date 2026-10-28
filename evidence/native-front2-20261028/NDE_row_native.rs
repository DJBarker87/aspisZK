fn row_canonical(q:QM31)->bool{q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(aspis_core::field::QM31::mul,crate::NDE_field::qm31)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_row(){
 let selectors=Selectors{high:kani::any(),low:kani::any()};
 let row:usize=kani::any();kani::assume(row<1024);
 let (left,right)=reference::row_operands_ref(&selectors.high,&selectors.low,row);
 kani::assume(row_canonical(left)&&row_canonical(right));
 unsafe{crate::NDE_field::NDE_COUNT=0;}
 let result=selectors.row(row);
 let ok=unsafe{crate::NDE_field::NDE_COUNT==1&&crate::NDE_field::NDE_LEFT==left&&crate::NDE_field::NDE_RIGHT==right&&crate::NDE_field::NDE_REPLY==result};
 assert!(ok != cfg!(NDE_invert));
}
// Diagnostics isolate the specification/log layer. They prove no native field
// arithmetic and earn no frontier-member credit.
#[kani::proof]
#[kani::unwind(6)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_stub_log(){
 let x:QM31=kani::any();let y:QM31=kani::any();kani::assume(row_canonical(x)&&row_canonical(y));
 unsafe{crate::NDE_field::NDE_COUNT=0;}
 let z=crate::NDE_field::qm31(x,y);
 let good=unsafe{crate::NDE_field::NDE_COUNT==1&&crate::NDE_field::NDE_LEFT==x&&crate::NDE_field::NDE_RIGHT==y&&crate::NDE_field::NDE_REPLY==z};
 assert!(good != cfg!(NDE_invert));
}
