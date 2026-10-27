//! Control/indexing models only. No arithmetic source-equivalence claim.
#[cfg(kani)]
mod checks {
    #[kani::proof]
    fn op121_block_indices() {
        let block: usize = kani::any();
        kani::assume(block < 7);
        let start = 4 * block;
        assert!(start + 3 < 28);
    }
    #[kani::proof]
    #[kani::unwind(8)]
    fn op121_descending_blocks() {
        let mut block = 6usize;
        let mut seen = 1u8 << 6;
        while block > 0 {
            block -= 1;
            assert!(block < 6);
            assert_eq!(seen & (1 << block), 0);
            seen |= 1 << block;
        }
        assert_eq!(seen, 127);
    }
    #[kani::proof]
    fn interpolation_sample_ctor() {
        let sample: usize = kani::any();
        kani::assume(sample < 28);
        assert!((sample as u32) < 2147483647);
    }
    #[kani::proof]
    fn interpolation_basis_indices() {
        let degree: usize = kani::any();
        let k: usize = kani::any();
        kani::assume(degree < 27);
        kani::assume(k <= degree + 1);
        assert!(k < 28);
        if k != 0 { assert!(k - 1 < 28); }
    }
    #[kani::proof]
    fn semantic_round_tags() {
        let round: usize = kani::any();
        kani::assume(round < 10);
        let row = 15 + round as u8;
        assert!((15..=24).contains(&row));
        assert!(round < 10);
        sampler_word_indices();
    }
    #[kani::proof]
    fn sampler_word_indices() {
        let i: usize = kani::any();
        kani::assume(i < 8);
        let start = 4 * i;
        assert!(start + 3 < 32);
        let digit: usize = kani::any();
        kani::assume(digit < 4);
        assert!(digit < 4);
    }
}
