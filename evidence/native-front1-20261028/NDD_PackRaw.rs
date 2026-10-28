// Exact frozen arithmetic spans, checked separately after the copy cut.
fn pack_raw_native0(v0:QM31,v1:QM31,v2:QM31,v3:QM31)->u64{let p=u64::from(P);let limb=|value:M31|u64::from(value.0);
    let c0_a = limb(v0.c0.a)
        + (p - limb(v1.c0.b))
        + 2 * limb(v2.c1.a)
        + (p - limb(v2.c1.b))
        + (p - limb(v3.c1.a))
        + (2 * p - 2 * limb(v3.c1.b));
c0_a
}
#[kani::proof] fn pack_raw0(){let x=[qm(kani::any()),qm(kani::any()),qm(kani::any()),qm(kani::any())];kani::assume(canonical(x[0])&&canonical(x[1])&&canonical(x[2])&&canonical(x[3]));let native=pack_raw_native0(x[0],x[1],x[2],x[3]);let spec=reference::raw_pack_ref([limbs(x[0]),limbs(x[1]),limbs(x[2]),limbs(x[3])],0);if cfg!(NDD_negative_raw){assert_ne!(native,spec);}else{assert_eq!(native,spec);}}
fn pack_raw_native1(v0:QM31,v1:QM31,v2:QM31,v3:QM31)->u64{let p=u64::from(P);let limb=|value:M31|u64::from(value.0);
    let c0_b = limb(v0.c0.b)
        + limb(v1.c0.a)
        + limb(v2.c1.a)
        + 2 * limb(v2.c1.b)
        + 2 * limb(v3.c1.a)
        + (p - limb(v3.c1.b));
c0_b
}
#[kani::proof] fn pack_raw1(){let x=[qm(kani::any()),qm(kani::any()),qm(kani::any()),qm(kani::any())];kani::assume(canonical(x[0])&&canonical(x[1])&&canonical(x[2])&&canonical(x[3]));let native=pack_raw_native1(x[0],x[1],x[2],x[3]);let spec=reference::raw_pack_ref([limbs(x[0]),limbs(x[1]),limbs(x[2]),limbs(x[3])],1);if cfg!(NDD_negative_raw){assert_ne!(native,spec);}else{assert_eq!(native,spec);}}
fn pack_raw_native2(v0:QM31,v1:QM31,v2:QM31,v3:QM31)->u64{let p=u64::from(P);let limb=|value:M31|u64::from(value.0);
    let c1_a = limb(v0.c1.a) + (p - limb(v1.c1.b)) + limb(v2.c0.a) + (p - limb(v3.c0.b));
c1_a
}
#[kani::proof] fn pack_raw2(){let x=[qm(kani::any()),qm(kani::any()),qm(kani::any()),qm(kani::any())];kani::assume(canonical(x[0])&&canonical(x[1])&&canonical(x[2])&&canonical(x[3]));let native=pack_raw_native2(x[0],x[1],x[2],x[3]);let spec=reference::raw_pack_ref([limbs(x[0]),limbs(x[1]),limbs(x[2]),limbs(x[3])],2);if cfg!(NDD_negative_raw){assert_ne!(native,spec);}else{assert_eq!(native,spec);}}
fn pack_raw_native3(v0:QM31,v1:QM31,v2:QM31,v3:QM31)->u64{let p=u64::from(P);let limb=|value:M31|u64::from(value.0);
    let c1_b = limb(v0.c1.b) + limb(v1.c1.a) + limb(v2.c0.b) + limb(v3.c0.a);
c1_b
}
#[kani::proof] fn pack_raw3(){let x=[qm(kani::any()),qm(kani::any()),qm(kani::any()),qm(kani::any())];kani::assume(canonical(x[0])&&canonical(x[1])&&canonical(x[2])&&canonical(x[3]));let native=pack_raw_native3(x[0],x[1],x[2],x[3]);let spec=reference::raw_pack_ref([limbs(x[0]),limbs(x[1]),limbs(x[2]),limbs(x[3])],3);if cfg!(NDD_negative_raw){assert_ne!(native,spec);}else{assert_eq!(native,spec);}}
