#[cfg(test)]
#[allow(non_snake_case)]
mod WAdm_tests {
    use aspis_core::{Digest32, field::{QM31 as K, WideExact as E}, circle::SecureCirclePoint};
    use aspis_r1_cost_probe::{verifier::{self, Prepared, Accumulator}, transport::Variant};
    use core::cell::Cell;
    #[derive(Clone, Copy)]
    struct WAdm_Hash<'a> { step: &'a Cell<usize>, proof: &'a [u8], public: &'a [u8] }
    impl Digest32 for WAdm_Hash<'_> {
        fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
            let n = self.step.get();
            match n {
                0 | 1 => {
                    assert_eq!(parts.len(), 1);
                    let expected = if n == 0 { self.proof } else { self.public };
                    assert_eq!(parts[0].as_ptr(), expected.as_ptr());
                    assert_eq!(parts[0].len(), expected.len());
                },
                2 => {
                    assert_eq!(parts.len(), 2);
                    assert_eq!(parts[0], b"UNPROVED:R1:checkpoint");
                    assert_eq!(parts[1].len(), 1736);
                    assert_eq!(&parts[1][..16], b"R1P2CKP2\x02\x0a\x01\x00\x00\x00\x00\x00");
                    assert_eq!(&parts[1][16..48], &[0x41; 32]);
                    assert_eq!(&parts[1][48..80], &[0x42; 32]);
                    assert!(parts[1][80..].iter().all(|b| *b == 0));
                },
                _ => panic!("unexpected digest call"),
            }
            self.step.set(n + 1);
            [0x41 + n as u8; 32]
        }
    }
    #[test]
    fn WAdm_shipped_writer_domain_nonempty() {
        let p = Prepared { variant: Variant::S2, roots: [[0; 32]; 2], gamma: E::ZERO,
            kappa: E::ZERO, alpha: [E::ZERO; 2], rho: K::ZERO, queries: [0; 22],
            semantic_alpha: [K::ZERO; 10], z: [SecureCirclePoint { x: K::ZERO, y: K::ZERO }; 2],
            claim: E::ZERO, state: [0; 32] };
        let a = Accumulator { weights: vec![K::ZERO; 64], rhs: E::ZERO, power: K::ZERO, next: 10 };
        let proof = [0; 57607]; let public = [0; 1880]; let step = Cell::new(0);
        let saved = verifier::checkpoint(&p, &a, &proof, &public, WAdm_Hash { step: &step, proof: &proof, public: &public });
        assert_eq!(saved.len(), 1768); assert_eq!(step.get(), 3);
        assert_eq!(&saved[1736..], &[0x43; 32]);
    }
}
