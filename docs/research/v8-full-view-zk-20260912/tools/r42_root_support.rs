//! Exhaustive, pinned source-root check, not a shared-oracle distribution proof.
use aspis_core::circle_fri::selected_circle_fiber_points_shared;
use aspis_core::field::M31;
use aspis_core::params::{CIRCLE_GEN, CIRCLE_LOG_ORDER};
use sha2::{Digest, Sha256};
const P: u64 = 2_147_483_647;
const N: usize = 1 << 18;
type Point = (u64, u64);
// Independent ordinary integer reduction, not the source's Mersenne kernels.
fn mul(a: Point, b: Point) -> Point {
    (((a.0*b.0)%P + P - (a.1*b.1)%P)%P,
     ((a.0*b.1)%P + (a.1*b.0)%P)%P)
}
fn pow(mut a: Point, mut n: u64) -> Point {
    let mut out=(1,0);
    while n!=0 {if n&1!=0 {out=mul(out,a);}a=mul(a,a);n>>=1;}
    out
}
fn main() {
    assert_eq!(CIRCLE_LOG_ORDER,31);
    let generator=(u64::from(CIRCLE_GEN.a.0),u64::from(CIRCLE_GEN.b.0));
    assert_eq!(generator,(2,1_268_011_823));
    assert_eq!(pow(generator,1<<31),(1,0));
    assert_ne!(pow(generator,1<<30),(1,0));
    let fibers:Vec<_>=(0..N as u32).collect();
    let actual=selected_circle_fiber_points_shared(20,&fibers).unwrap();
    assert_eq!(actual.len(),N);
    let mut point=pow(generator,1<<10);
    let step=pow(generator,1<<12);
    let mut roots=vec![0u32;N];let mut wrong_order=0;
    for natural in 0..N {
        let stored=natural.reverse_bits()>>(usize::BITS-18);
        let got=actual[stored];
        assert_eq!((u64::from(got.x.0),u64::from(got.y.0)),point);
        assert_eq!((point.0*point.0%P+point.1*point.1%P)%P,1);
        let reference=(2*(point.0*point.0%P)+P-1)%P;
        let root=got.x.mul(got.x).mul(M31(2)).sub(M31::ONE).0;
        assert_eq!(u64::from(root),reference);assert!(root<P as u32);
        assert_ne!(root,1);roots[stored]=root;
        if actual[natural]!=got {wrong_order+=1;}
        point=mul(point,step);
    }
    let mut sorted=roots.clone();sorted.sort_unstable();sorted.dedup();
    assert_eq!(sorted.len(),N);assert!(wrong_order>0);
    let mut duplicated=roots.clone();duplicated[1]=duplicated[0];
    duplicated.sort_unstable();duplicated.dedup();assert_eq!(duplicated.len(),N-1);
    let repeated=selected_circle_fiber_points_shared(20,&[7,7]).unwrap();
    assert_eq!(repeated[0],repeated[1]);
    assert!(selected_circle_fiber_points_shared(20,&[N as u32]).is_err());
    assert!(selected_circle_fiber_points_shared(20,&[u32::MAX]).is_err());
    let mut hasher=Sha256::new();for root in &roots {hasher.update(root.to_le_bytes());}
    println!("R42_ROOT_SUPPORT roots={} source_points={} integer_reference_checks={} unique={} wrong_order_negative={} duplicate_negative=1 out_of_range_negative=2 ordered_root_sha256={:x} sampler_law=false full_privacy=false",
        N,N,N,sorted.len(),wrong_order,hasher.finalize());
}
