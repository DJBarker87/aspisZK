//! Full-source differential for unrolled WideExact::from_le_bytes and from_limbs.
#![allow(dead_code, unexpected_cfgs)]

extern crate alloc;
mod baseline;
mod field;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Outcome<T> { Panic, None, Value(T) }
#[derive(Default)]
struct Counts { input_vectors: usize, parser_calls: usize, limbs_helper_vectors: usize, limbs_helper_calls: usize }
fn observe(f: impl FnOnce() -> Option<[u32; 8]>) -> Outcome<[u32; 8]> {
    match catch_unwind(AssertUnwindSafe(f)) { Err(_) => Outcome::Panic, Ok(None) => Outcome::None, Ok(Some(x)) => Outcome::Value(x) }
}
fn observe_baseline_limbs(x: [u32; 8]) -> Outcome<[u32; 8]> {
    match catch_unwind(AssertUnwindSafe(|| baseline::WideExact::from_limbs(x).map(|v| v.to_limbs()))) { Err(_) => Outcome::Panic, Ok(None) => Outcome::None, Ok(Some(v)) => Outcome::Value(v) }
}
fn observe_candidate_limbs(x: [u32; 8]) -> Outcome<[u32; 8]> {
    match catch_unwind(AssertUnwindSafe(|| field::WideExact::from_limbs(x).map(|v| v.to_limbs()))) { Err(_) => Outcome::Panic, Ok(None) => Outcome::None, Ok(Some(v)) => Outcome::Value(v) }
}
fn assert_no_panic<T: std::fmt::Debug>(outcome: &Outcome<T>, side: &str, bytes: &[u8]) {
    assert!(!matches!(outcome, Outcome::Panic), "{side} panicked: len={} bytes={bytes:?}", bytes.len());
}
fn parse_pair(bytes: &[u8], counts: &mut Counts) -> Outcome<[u32; 8]> {
    counts.input_vectors += 1;
    counts.parser_calls += 2;
    let b = observe(|| baseline::WideExact::from_le_bytes(bytes).map(|x| x.to_limbs()));
    let c = observe(|| field::WideExact::from_le_bytes(bytes).map(|x| x.to_limbs()));
    assert_no_panic(&b, "baseline parser", bytes);
    assert_no_panic(&c, "candidate parser", bytes);
    assert_eq!(c, b, "parser results differ for len={} bytes={bytes:?}", bytes.len());
    if bytes.len() == 32 {
        let limbs: [u32; 8] = std::array::from_fn(|i| u32::from_le_bytes(bytes[i*4..i*4+4].try_into().unwrap()));
        counts.limbs_helper_vectors += 1;
        counts.limbs_helper_calls += 2;
        let bl = observe_baseline_limbs(limbs);
        let cl = observe_candidate_limbs(limbs);
        assert_no_panic(&bl, "baseline from_limbs", bytes);
        assert_no_panic(&cl, "candidate from_limbs", bytes);
        assert_eq!(cl, bl, "from_limbs results differ for bytes={bytes:?}");
        assert_eq!(b, bl, "baseline parser/from_limbs differ for bytes={bytes:?}");
        assert_eq!(c, cl, "candidate parser/from_limbs differ for bytes={bytes:?}");
    }
    c
}
fn put_limb(bytes: &mut [u8; 32], limb: usize, value: u32) { bytes[limb*4..limb*4+4].copy_from_slice(&value.to_le_bytes()); }
fn limb_vector(values: &[u32; 8]) -> [u8;32] { let mut b=[0;32]; for (i,v) in values.iter().copied().enumerate(){put_limb(&mut b,i,v)} b }
fn boundary_cases(c: &mut Counts) {
    const P:u32=0x7fff_ffff; let vals=[0,1,P-1,P,P+1,u32::MAX];
    for len in 0..=64 { parse_pair(&vec![0;len],c); }
    for limb in 0..8 { for v in vals { let mut b=[0;32];put_limb(&mut b,limb,v);parse_pair(&b,c); } }
    for i in 0..8 { for j in i+1..8 { for a in vals { for bval in vals { let mut b=[0;32];put_limb(&mut b,i,a);put_limb(&mut b,j,bval);parse_pair(&b,c); } } } }
    for v in vals { parse_pair(&limb_vector(&[v;8]),c); }
}
fn every_single_byte(c:&mut Counts){ for pos in 0..32 { for v in 0..=u8::MAX { let mut b=[0;32];b[pos]=v;parse_pair(&b,c); } } }
fn seeded_random(c:&mut Counts){let mut s=0x5749_4445_5041_5253u64;for len in 0..=64{for _ in 0..256{let mut b=vec![0;len];for x in &mut b{s^=s>>12;s^=s<<25;s^=s>>27;*x=(s.wrapping_mul(0x2545_f491_4f6c_dd1d)>>56) as u8;}parse_pair(&b,c);}}}
fn canonical(c:&mut Counts){const P:u32=0x7fff_ffff;let mut s=0x4341_4e4f_4e49_4341u64;for _ in 0..4096{let limbs=std::array::from_fn(|_|{s^=s>>12;s^=s<<25;s^=s>>27;((s.wrapping_mul(0x2545_f491_4f6c_dd1d)>>32)as u32)%P});let bytes=limb_vector(&limbs);let parsed=parse_pair(&bytes,c);assert_eq!(parsed,Outcome::Value(limbs),"canonical parser roundtrip failed; parse_pair also checks both from_limbs implementations");}}
#[test]
fn unrolled_wideexact_parser_and_limbs_match_baseline(){std::panic::set_hook(Box::new(|_|{}));let mut c=Counts::default();boundary_cases(&mut c);every_single_byte(&mut c);seeded_random(&mut c);canonical(&mut c);assert_eq!(c.input_vectors,30055);assert_eq!(c.parser_calls,60110);assert_eq!(c.limbs_helper_vectors,13607);assert_eq!(c.limbs_helper_calls,27214);eprintln!("input vectors: {}; parser calls: {} (two per vector); exact-32-byte from_limbs vectors: {}; from_limbs calls: {} (two per vector)",c.input_vectors,c.parser_calls,c.limbs_helper_vectors,c.limbs_helper_calls);}
