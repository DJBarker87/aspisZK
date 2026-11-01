//! Direct-source embedding and equality contracts for scalar boundaries.
use aspis_core::{field::{WideExact as E,QM31 as Q,CM31 as C,M31,P},r0::CodeField};
#[kani::proof]
#[kani::unwind(40)]
fn raw_base_embeddings() {
    let raw:u32=kani::any();let expected=raw%P;
    assert_eq!(<M31 as CodeField>::from_m31(M31(raw)),M31(expected));
    let c=<C as CodeField>::from_m31(M31(raw));assert_eq!([c.a.0,c.b.0],[expected,0]);
    let q=<Q as CodeField>::from_m31(M31(raw));
    assert_eq!([q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0],[expected,0,0,0]);
    let e=<E as CodeField>::from_m31(M31(raw));assert_eq!(e.to_limbs(),[expected,0,0,0,0,0,0,0]);
}
#[kani::proof]
#[kani::unwind(40)]
fn canonical_scalar_equalities() {
    let a:[u32;8]=kani::any();let b:[u32;8]=kani::any();
    for x in a {kani::assume(x<P);}for x in b {kani::assume(x<P);}
    let x=E::from_limbs(a).unwrap();let y=E::from_limbs(b).unwrap();
    assert_eq!(x==y,a==b);
    assert_eq!(x.c0()==y.c0(),[a[0],a[1],a[2],a[3]]==[b[0],b[1],b[2],b[3]]);
    assert_eq!(x.c0().c0==y.c0().c0,[a[0],a[1]]==[b[0],b[1]]);
    assert_eq!(x.c0().c0.a==y.c0().c0.a,a[0]==b[0]);
}
