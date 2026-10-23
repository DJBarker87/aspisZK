use aspis_core::field::{QM31,CM31,M31,P};
fn canonical()->QM31 {
    let a:[u32;4]=kani::any();for x in a {kani::assume(x<P);}
    QM31{c0:CM31::new(M31(a[0]),M31(a[1])),c1:CM31::new(M31(a[2]),M31(a[3]))}
}
#[kani::proof]
#[kani::unwind(60)]
fn exact_d_tail() {
    let initial=canonical();let mut dc=[QM31::ZERO;1024];
    for i in 0..56 {dc[i]=canonical();}
    assert_eq!(super::dtail_source::actual(initial,&dc),super::dtail_source::expected(initial,&dc));
}
