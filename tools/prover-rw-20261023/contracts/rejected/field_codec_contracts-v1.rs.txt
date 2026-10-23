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
#[kani::proof]
#[kani::unwind(40)]
fn arbitrary_field_decoders() {
    let bytes:[u8;32]=kani::any();
    let mut limbs=[0u32;8];
    let mut valid=true;let mut qvalid=true;
    for i in 0..8 {
        limbs[i]=u32::from_le_bytes([bytes[4*i],bytes[4*i+1],bytes[4*i+2],bytes[4*i+3]]);
        valid &= limbs[i]<P;
        if i<4 {qvalid &= limbs[i]<P;}
    }
    let decoded=E::from_le_bytes(&bytes);
    assert_eq!(decoded.is_some(),valid);
    if let Some(e)=decoded {assert_eq!(e.to_limbs(),limbs);}
    let decoded_q=QM31::from_le_bytes(&bytes[..16]);
    assert_eq!(decoded_q.is_some(),qvalid);
    if let Some(q)=decoded_q {assert_eq!([q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0],[limbs[0],limbs[1],limbs[2],limbs[3]]);}
    assert_eq!(E::from_le_bytes(&bytes[..31]),None);
    assert_eq!(QM31::from_le_bytes(&bytes[..15]),None);
}
