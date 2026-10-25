#![allow(non_snake_case, non_camel_case_types)]
use aspis_core::{Digest32, field::{QM31 as K, WideExact as E}};
use aspis_r1_cost_probe::verifier::Prepared;

pub struct WAdm_Fields {
    pub roots: [[u8; 32]; 2], pub state: [u8; 32], pub early: [E; 4],
    pub rho: K, pub queries: [u32; 22], pub semantic: [K; 10], pub coordinates: [K; 4],
    pub tail: [E; 2], pub power: K,
}
pub fn WAdm_fields(p: &Prepared, rhs: E, power: K) -> WAdm_Fields {
    WAdm_Fields { roots: p.roots, state: p.state, early: [p.gamma, p.kappa, p.alpha[0], p.alpha[1]],
        rho: p.rho, queries: p.queries, semantic: p.semantic_alpha,
        coordinates: [p.z[0].x, p.z[0].y, p.z[1].x, p.z[1].y], tail: [p.claim, rhs], power }
}
#[inline(never)]
pub fn WAdm_roots(mut out: Vec<u8>, roots: [[u8; 32]; 2]) -> Vec<u8> {
    for root in roots { out.extend_from_slice(&root); } out
}
#[inline(never)]
pub fn WAdm_early(mut out: Vec<u8>, xs: [E; 4]) -> Vec<u8> {
    for x in xs { out.extend_from_slice(&x.to_le_bytes()); } out
}
#[inline(never)]
pub fn WAdm_tail(mut out: Vec<u8>, xs: [E; 2]) -> Vec<u8> {
    for x in xs { out.extend_from_slice(&x.to_le_bytes()); } out
}
#[inline(never)]
pub fn WAdm_putK(mut out: Vec<u8>, x: K) -> Vec<u8> {
    let mut b = [0; 16]; x.write_le_bytes(&mut b); out.extend_from_slice(&b); out
}
#[inline(never)]
pub fn WAdm_queries(mut out: Vec<u8>, xs: [u32; 22]) -> Vec<u8> {
    for x in xs { out.extend_from_slice(&x.to_le_bytes()); } out
}
#[inline(never)]
pub fn WAdm_semantic(mut out: Vec<u8>, xs: [K; 10]) -> Vec<u8> {
    for x in xs { out = WAdm_putK(out, x); } out
}
#[inline(never)]
pub fn WAdm_coordinates(mut out: Vec<u8>, xs: [K; 4]) -> Vec<u8> {
    for x in xs { out = WAdm_putK(out, x); } out
}
#[inline(never)]
pub fn WAdm_weights(mut out: Vec<u8>, xs: Vec<K>) -> Vec<u8> {
    for x in xs { out = WAdm_putK(out, x); } out
}
// Bounded source model only: S2 / next10 / weights64 are established on the
// same accepted run before native substitution, never inferred from this model.
#[inline(never)]
pub fn WAdm_checkpoint<H: Digest32>(f: WAdm_Fields, weights: Vec<K>, proof: &[u8], public: &[u8], hash: H) -> Vec<u8> {
    assert_eq!(weights.len(), 64);
    let mut out = Vec::with_capacity(1768);
    out.extend_from_slice(b"R1P2CKP2"); out.extend_from_slice(&[2, 10, 1, 0, 0, 0, 0, 0]);
    out.extend_from_slice(&hash.digest(&[proof])); out.extend_from_slice(&hash.digest(&[public]));
    out.extend_from_slice(&f.state);
    out = WAdm_roots(out, f.roots); out = WAdm_early(out, f.early); out = WAdm_putK(out, f.rho);
    out = WAdm_queries(out, f.queries); out = WAdm_semantic(out, f.semantic);
    out = WAdm_coordinates(out, f.coordinates); out = WAdm_tail(out, f.tail); out = WAdm_putK(out, f.power);
    out = WAdm_weights(out, weights);
    let sum = hash.digest(&[b"UNPROVED:R1:checkpoint", &out]); out.extend_from_slice(&sum);
    assert_eq!(out.len(), 1768); out
}

#[cfg(kani)]
mod WAdm_proofs {
    use super::*;
    use aspis_core::{field::{M31, CM31}, circle::SecureCirclePoint};
    use aspis_r1_cost_probe::{verifier::{self, Prepared, Accumulator}, transport::Variant};
    use core::cell::Cell;
    fn WAdm_anyK() -> K {
        let x: [u32; 4] = kani::any();
        K { c0: CM31 { a: M31(x[0]), b: M31(x[1]) }, c1: CM31 { a: M31(x[2]), b: M31(x[3]) } }
    }
    fn WAdm_anyE() -> E {
        let x: [u32; 8] = kani::any(); for limb in x { kani::assume(limb < 0x7fffffff); }
        E::from_limbs(x).unwrap()
    }
    #[derive(Clone, Copy)]
    struct WAdm_Hash<'a> { step: &'a Cell<usize>, answers: [[u8; 32]; 3], proof: &'a [u8], public: &'a [u8],
        index: usize, native_body: &'a Cell<u8>, model: bool }
    impl Digest32 for WAdm_Hash<'_> {
        fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
            let n = self.step.get(); assert!(n < 3);
            if n < 2 {
                assert_eq!(parts.len(), 1); let expected = if n == 0 { self.proof } else { self.public };
                assert_eq!(parts[0].as_ptr(), expected.as_ptr()); assert_eq!(parts[0].len(), expected.len());
            } else {
                assert_eq!(parts.len(), 2); assert_eq!(parts[0], b"UNPROVED:R1:checkpoint"); assert_eq!(parts[1].len(), 1736);
                if self.model { assert_eq!(parts[1][self.index], self.native_body.get()); }
                else { self.native_body.set(parts[1][self.index]); }
            }
            self.step.set(n + 1); self.answers[n]
        }
    }
    #[kani::proof]
    #[kani::unwind(70)]
    fn WAdm_native_matches_fissioned_source() {
        let p = Prepared { variant: Variant::S2, roots: kani::any(), state: kani::any(),
            gamma: WAdm_anyE(), kappa: WAdm_anyE(), alpha: [WAdm_anyE(), WAdm_anyE()], rho: WAdm_anyK(),
            queries: kani::any(), semantic_alpha: core::array::from_fn(|_| WAdm_anyK()),
            z: core::array::from_fn(|_| SecureCirclePoint { x: WAdm_anyK(), y: WAdm_anyK() }), claim: WAdm_anyE() };
        let a = Accumulator { weights: (0..64).map(|_| WAdm_anyK()).collect(), rhs: WAdm_anyE(), power: WAdm_anyK(), next: 10 };
        let proof: [u8; 57607] = kani::any(); let public: [u8; 1880] = kani::any(); let answers = kani::any();
        let i: usize = kani::any(); kani::assume(i < 1736); let j: usize = kani::any(); kani::assume(j < 1768);
        let step = Cell::new(0); let native_body = Cell::new(0);
        let hash = WAdm_Hash { step: &step, answers, proof: &proof, public: &public, index: i, native_body: &native_body, model: false };
        let got = verifier::checkpoint(&p, &a, &proof, &public, hash); assert_eq!(step.get(), 3); step.set(0);
        let want = WAdm_checkpoint(WAdm_fields(&p, a.rhs, a.power), a.weights.clone(), &proof, &public, WAdm_Hash { model: true, ..hash });
        assert_eq!(step.get(), 3); assert_eq!(got.len(), 1768); assert_eq!(want.len(), 1768); assert_eq!(got[j], want[j]);
    }
}
