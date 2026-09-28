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
    for limb in 0..8 {for bad in [P,P+1,u32::MAX] {
        let mut l=[1u32;8];l[limb]=bad;
        let bytes=|v:&[u32]| {let mut b=[0u8;16];for (i,x) in v.iter().enumerate(){b[4*i..4*i+4].copy_from_slice(&x.to_le_bytes());}b};
        let a=K{c0:CM31::new(M31(l[0]),M31(l[1])),c1:CM31::new(M31(l[2]),M31(l[3]))};
        let b=K{c0:CM31::new(M31(l[4]),M31(l[5])),c1:CM31::new(M31(l[6]),M31(l[7]))};
        let mk=|v:&[u32]|r23_reference_field::QM31{c0:r23_reference_field::CM31::new(r23_reference_field::M31(v[0]),r23_reference_field::M31(v[1])),c1:r23_reference_field::CM31::new(r23_reference_field::M31(v[2]),r23_reference_field::M31(v[3]))};
        let original=std::panic::catch_unwind(|| {let mut v=[0;16];mk(&l[..4]).mul(mk(&l[4..])).write_le_bytes(&mut v);v});
        let actual=std::panic::catch_unwind(|| {let mut v=[0;16];a.mul(b).write_le_bytes(&mut v);v});
        let prepared_original=std::panic::catch_unwind(|| {let mut v=[0;16];r23_reference_field::PreparedQm31Multiplier::new(mk(&l[..4])).mul(mk(&l[4..])).write_le_bytes(&mut v);v});
        let prepared_actual=std::panic::catch_unwind(|| {let mut v=[0;16];aspis_core::field::PreparedQm31Multiplier::new(a).mul(b).write_le_bytes(&mut v);v});
        match(prepared_original,prepared_actual){(Ok(x),Ok(y))=>assert_eq!(x,y),(Err(_),Err(_))=>(),_=>panic!("prepared raw outcome changed")}

        match (original,actual) {(Ok(x),Ok(y))=>assert_eq!(x,y),(Err(_),Err(_))=>(),_=>panic!("invalid constructor outcome changed")}
        let _=bytes;
    }}
    println!("R24_QM invalid_constructor_cases=24 old_fallback_retained=true");
    std::panic::set_hook(hook);
    let mut seed=0x9c23_2026_abcdef01u64;
    let mut sample=|| {let mut limb=|| {seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;M31(seed as u32%P)};K{c0:CM31::new(limb(),limb()),c1:CM31::new(limb(),limb())}};
    let encode=|k:K| {let mut b=[0;16];k.write_le_bytes(&mut b);b};
    let reference=|k:K|R::from_le_bytes(&encode(k)).unwrap();
    let mut compare=|a:K,b:K| {
        let ar=reference(a);let br=reference(b);
        use aspis_core::field as f;
        let aa=[a,b,a.neg(),b.neg()];let bb=[b,a,b.neg(),a.neg()];
        let ra=[ar,br,ar.neg(),br.neg()];let rb=[br,ar,br.neg(),ar.neg()];
        let comparisons=[
            (f::qm31_sum_products2([aa[0],aa[1]],[bb[0],bb[1]]),r23_reference_field::qm31_sum_products2([ra[0],ra[1]],[rb[0],rb[1]])),
            (f::qm31_sum_products3([aa[0],aa[1],aa[2]],[bb[0],bb[1],bb[2]]),r23_reference_field::qm31_sum_products3([ra[0],ra[1],ra[2]],[rb[0],rb[1],rb[2]])),
            (f::qm31_sum_products4(aa,bb),r23_reference_field::qm31_sum_products4(ra,rb))];
        for (x,y) in comparisons {let mut bytes=[0;16];y.write_le_bytes(&mut bytes);assert_eq!(encode(x),bytes);}

        for (x,y) in [(a.mul(b),ar.mul(br)),(a.square(),ar.square()),(aspis_core::field::PreparedQm31Multiplier::new(a).mul(b),r23_reference_field::PreparedQm31Multiplier::new(ar).mul(br))] {
            let mut bytes=[0;16];y.write_le_bytes(&mut bytes);assert_eq!(encode(x),bytes);
        }
    };
    let edge=[0,1,2,P/2,P-2,P-1];
    for a in edge {for b in edge {for c in edge {for d in edge {
        let k=K{c0:CM31::new(M31(a),M31(b)),c1:CM31::new(M31(c),M31(d))};compare(k,k.neg());
    }}}}
    for _ in 0..200_000 {compare(sample(),sample());}
    println!("R23_FIELD random_pairs=200000 boundary_pairs=1296 operations_per_pair=6 dot_arities=2,3,4 raw_product_cases=64 checked_overflow_panics={panics} reference=unmodified_R20_field");
}
