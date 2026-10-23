//! Direct shipped CT field calls; byte order, canonical decoding and embedding.
use aspis_core::field::{WideExact as E,QM31,CM31,M31,P};
#[kani::proof]
#[kani::unwind(40)]
fn exact_full_width_codec() {
    let limbs:[u32;8]=kani::any();
    for limb in limbs {kani::assume(limb<P);}
    let e=E::from_limbs(limbs).unwrap();
    assert_eq!(e.to_limbs(),limbs);
    let bytes=e.to_le_bytes();
    for limb in 0..8 {
        let word=limbs[limb].to_le_bytes();
        for byte in 0..4 {assert_eq!(bytes[4*limb+byte],word[byte]);}
    }
    assert_eq!(E::from_le_bytes(&bytes),Some(e));
}
#[kani::proof]
#[kani::unwind(40)]
fn raw_qm31_embedding_codec() {
    let raw:[u32;4]=kani::any();
    let q=QM31{c0:CM31::new(M31(raw[0]),M31(raw[1])),c1:CM31::new(M31(raw[2]),M31(raw[3]))};
    let e=E::from_qm31(q);
    let limbs=e.to_limbs();
    for i in 0..4 {assert_eq!(limbs[i],raw[i]%P);assert_eq!(limbs[i+4],0);}
    let bytes=e.to_le_bytes();
    assert_eq!(E::from_le_bytes(&bytes),Some(e));
    assert_eq!(QM31::from_le_bytes(&bytes[..16]),Some(e.c0()));
    assert_eq!(e.c1(),QM31::ZERO);
}
