#[cfg(test)]
mod tests {
    use aspis_core::{Digest32, circle::SecureCirclePoint, field::{QM31 as K, WideExact as E}};
    use aspis_r1_cost_probe::{transport::Variant, verifier::{self, Accumulator, Prepared}};
    use std::cell::Cell;
    #[derive(Clone, Copy)]
    struct Hash<'a>(&'a Cell<usize>);
    impl Digest32 for Hash<'_> {
        fn digest(&self, _: &[&[u8]]) -> [u8; 32] {
            self.0.set(self.0.get() + 1);
            [0; 32]
        }
    }
    // This is a typed operation-domain counterexample, not a reachable-spend
    // witness or a verifier vulnerability. All fields are canonical and S2.
    #[test]
    fn s2_empty_weights_writer_panics_after_three_reads() {
        let p = Prepared {
            variant: Variant::S2, roots: [[0;32];2], gamma: E::ZERO,
            kappa: E::ZERO, alpha: [E::ZERO;2], rho: K::ZERO,
            queries: [0;22], semantic_alpha: [K::ZERO;10],
            z: [SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],
            claim: E::ZERO, state: [0;32],
        };
        let a = Accumulator { weights: vec![], rhs: E::ZERO, power: K::ONE, next: 10 };
        let calls = Cell::new(0);
        let got = std::panic::catch_unwind(std::panic::AssertUnwindSafe(||
            verifier::checkpoint(&p, &a, &[0;3], &[0;5], Hash(&calls))));
        assert!(got.is_err(), "native writer must reject the short weight domain");
        assert_eq!(calls.get(),3);
        println!("S2 canonical empty weights: native panic at size assertion after 3 reads; selector reference always emits 1768 bytes");
    }
    // The complement of S1S7S8StateProvenance is not a rejection domain.
    // Keep canonical fields and the correct width, but violate next=10.
    #[test]
    fn s2_full_weights_outside_provenance_writer_returns() {
        let mut p = Prepared {
            variant: Variant::S2, roots: [[0;32];2], gamma: E::ZERO,
            kappa: E::ZERO, alpha: [E::ZERO;2], rho: K::ZERO,
            queries: core::array::from_fn(|j| j as u32), semantic_alpha: [K::ZERO;10],
            z: [SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],
            claim: E::ZERO, state: [0;32],
        };
        let mut a = Accumulator { weights: vec![K::ZERO;64], rhs: E::ZERO, power: K::ONE, next: 11 };
        let calls = Cell::new(0);
        let saved = verifier::checkpoint(&p, &a, &[0;57607], &[0;1880], Hash(&calls));
        assert_eq!(saved.len(),1768);
        assert_eq!(saved[9],11);
        assert_eq!(calls.get(),3);
        println!("OUTSIDE provenance.next: S2/64 weights/next11 writer returns 1768 bytes after 3 reads (production-sized buffers)");

        // Separately violate queriesBound while retaining next=10.
        a.next = 10;
        p.queries[0] = 1 << 18;
        calls.set(0);
        let saved = verifier::checkpoint(&p, &a, &[0;57607], &[0;1880], Hash(&calls));
        assert_eq!(saved.len(),1768);
        assert_eq!(saved[9],10);
        assert_eq!(calls.get(),3);
        println!("OUTSIDE provenance.queriesBound: S2/64 weights/next10/query262144 writer returns 1768 bytes after 3 reads");
    }

}
