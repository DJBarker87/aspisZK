#![allow(dead_code, unexpected_cfgs)]
use aspis_core::field::{M31, CM31, QM31 as K, WideExact as E};
use aspis_r1_cost_probe::verifier::Error;
include!("reader-source.rs");

#[cfg(kani)] mod proofs {
use super::*;
// Every byte is symbolic. The seventeenth byte belongs to the next section.
#[kani::proof]
#[kani::unwind(18)]
fn k_exact_section() {
    let b: [u8; 17] = kani::any();
    let mut r = Reader { bytes: &b, at: 0 };
    let got = r.k();
    assert_eq!(r.at, 16);
    let limbs = [u32::from_le_bytes(b[0..4].try_into().unwrap()),
        u32::from_le_bytes(b[4..8].try_into().unwrap()),
        u32::from_le_bytes(b[8..12].try_into().unwrap()),
        u32::from_le_bytes(b[12..16].try_into().unwrap())];
    let canonical = limbs[0] < 0x7fffffff && limbs[1] < 0x7fffffff &&
        limbs[2] < 0x7fffffff && limbs[3] < 0x7fffffff;
    assert_eq!(got.is_ok(), canonical);
    if let Ok(k) = got {
        assert_eq!([k.c0.a.0,k.c0.b.0,k.c1.a.0,k.c1.b.0], limbs);
        let mut encoded = [0;16]; k.write_le_bytes(&mut encoded);
        assert_eq!(encoded.as_slice(), &b[..16]);
    }
}
#[kani::proof]
#[kani::unwind(18)]
fn k_roundtrip() {
    let x: [u32;4] = kani::any();
    kani::assume(x[0] < 0x7fffffff && x[1] < 0x7fffffff && x[2] < 0x7fffffff && x[3] < 0x7fffffff);
    let k = K { c0: CM31 { a:M31(x[0]),b:M31(x[1]) }, c1: CM31 { a:M31(x[2]),b:M31(x[3]) } };
    let mut bytes = [0;16]; k.write_le_bytes(&mut bytes);
    let mut r = Reader { bytes:&bytes,at:0 };
    assert_eq!(r.k(), Ok(k)); assert_eq!(r.at,16);
}
#[kani::proof]
#[kani::unwind(34)]
fn e_exact_section() {
    let b: [u8;33] = kani::any();
    let mut r = Reader { bytes:&b,at:0 };
    let got = r.e(); assert_eq!(r.at,32);
    let mut limbs=[0u32;8];
    for i in 0..8 { limbs[i] = u32::from_le_bytes(b[4*i..4*i+4].try_into().unwrap()); }
    let mut canonical=true;
    for limb in limbs { canonical &= limb < 0x7fffffff; }
    assert_eq!(got.is_ok(),canonical);
    if let Ok(e) = got { assert_eq!(e.to_limbs(),limbs); assert_eq!(e.to_le_bytes().as_slice(), &b[..32]); }
}
#[kani::proof]
#[kani::unwind(34)]
fn e_roundtrip() {
    let limbs:[u32;8]=kani::any();
    for limb in limbs { kani::assume(limb<0x7fffffff); }
    let e=E::from_limbs(limbs).unwrap(); let bytes=e.to_le_bytes();
    let mut r=Reader{bytes:&bytes,at:0};
    assert_eq!(r.e(),Ok(e)); assert_eq!(r.at,32);
}
}
