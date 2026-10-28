fn row_canonical(q:QM31)->bool{q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(aspis_core::field::QM31::mul,crate::NDE_field::qm31)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_row(){
 let h:[[u32;4];64]=kani::any();let l:[[u32;4];16]=kani::any();
 let conv=|a:[u32;4]|to_native(reference::Q{c0:reference::C{a:a[0],b:a[1]},c1:reference::C{a:a[2],b:a[3]}});
 let selectors=Selectors{high:h.map(conv),low:l.map(conv)};
 let row:usize=kani::any();kani::assume(row<1024);
 let (left,right)=reference::row_operands_ref(&selectors.high,&selectors.low,row);
 kani::assume(row_canonical(left)&&row_canonical(right));
 unsafe{crate::NDE_field::NDE_COUNT=0;}
 let result=selectors.row(row);
 let ok=unsafe{crate::NDE_field::NDE_COUNT==1&&crate::NDE_field::NDE_LEFT==left&&crate::NDE_field::NDE_RIGHT==right&&crate::NDE_field::NDE_REPLY==result};
 assert!(ok != cfg!(NDE_invert));
}
