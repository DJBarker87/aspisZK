// Host-only differential gate against the exact unmodified staged field source.
mod r23_reference_field;
fn r23_field_check() {
    use aspis_core::field::{QM31 as K,CM31,M31,P,r23_product_u32_bounded};
    use r23_reference_field::QM31 as R;
    let values=[0,1,u64::from(P-1),u64::from(P),u64::from(u32::MAX),1u64<<32,(1u64<<32)+1,u64::MAX];
    let mut panics=0;
    let hook=std::panic::take_hook();std::panic::set_hook(Box::new(|_|{}));
    for a in values {for b in values {
        let actual=std::panic::catch_unwind(||r23_product_u32_bounded(std::hint::black_box(a),std::hint::black_box(b)));
        match a.checked_mul(b) {Some(n)=>assert_eq!(actual.unwrap(),n),None=>{assert!(actual.is_err());panics+=1;}}
    }}
    std::panic::set_hook(hook);
    let mut seed=0x9c23_2026_abcdef01u64;
    let mut sample=|| {let mut limb=|| {seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;M31(seed as u32%P)};K{c0:CM31::new(limb(),limb()),c1:CM31::new(limb(),limb())}};
    let encode=|k:K| {let mut b=[0;16];k.write_le_bytes(&mut b);b};
    let reference=|k:K|R::from_le_bytes(&encode(k)).unwrap();
    let mut compare=|a:K,b:K| {
        let ar=reference(a);let br=reference(b);
        for (x,y) in [(a.mul(b),ar.mul(br)),(a.square(),ar.square())] {
            let mut bytes=[0;16];y.write_le_bytes(&mut bytes);assert_eq!(encode(x),bytes);
        }
    };
    let edge=[0,1,2,P/2,P-2,P-1];
    for a in edge {for b in edge {for c in edge {for d in edge {
        let k=K{c0:CM31::new(M31(a),M31(b)),c1:CM31::new(M31(c),M31(d))};compare(k,k.neg());
    }}}}
    for _ in 0..200_000 {compare(sample(),sample());}
    println!("R23_FIELD random_pairs=200000 boundary_pairs=1296 operations_per_pair=2 raw_product_cases=64 checked_overflow_panics={panics} reference=unmodified_R20_field");
}
