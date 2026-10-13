use aspis_core::field::{WideExact, P};
use aspis_r1_cost_probe::sampler::{gamma_sample, ordinary_sample};

const P8: [u32; 8] = [
    1,
    0xffff_fffc,
    6,
    0x5fff_fff9,
    0x4000_0004,
    0x6fff_fffe,
    0xf000_0000,
    0x00ff_ffff,
];

const P8_MINUS_ONE: [u32; 8] = [
    0,
    0xffff_fffc,
    6,
    0x5fff_fff9,
    0x4000_0004,
    0x6fff_fffe,
    0xf000_0000,
    0x00ff_ffff,
];

fn block_from_words(words: [u32; 8]) -> [u8; 32] {
    core::array::from_fn(|i| words[i / 4].to_le_bytes()[i % 4])
}

fn increment(words: &mut [u32; 8]) {
    for word in words {
        let (next, carry) = word.overflowing_add(1);
        *word = next;
        if !carry {
            return;
        }
    }
}

fn decrement(words: &mut [u32; 8]) {
    for word in words {
        let (next, borrow) = word.overflowing_sub(1);
        *word = next;
        if !borrow {
            return;
        }
    }
}

fn assert_matches_core(block: &[u8; 32]) {
    let ordinary = ordinary_sample(block);
    let gamma = gamma_sample(block);
    assert_eq!(
        ordinary.to_limbs(),
        aspis_core::r0_transcript::ordinary_sample(block).to_limbs()
    );
    assert_eq!(
        gamma.to_limbs(),
        aspis_core::r0_transcript::gamma_sample(block).to_limbs()
    );
    assert!(ordinary.to_limbs().iter().all(|&limb| limb < P));
    assert!(gamma.to_limbs().iter().all(|&limb| limb < P));
    assert_ne!(gamma, WideExact::ZERO);
}

#[test]
fn optimized_samplers_match_frozen_core_at_modulus_boundaries() {
    let mut cases = vec![[0; 32], [0xff; 32]];
    let mut p8_minus_two = P8_MINUS_ONE;
    decrement(&mut p8_minus_two);
    let mut after_p8 = P8;
    increment(&mut after_p8);

    cases.extend([
        block_from_words(p8_minus_two),
        block_from_words(P8_MINUS_ONE),
        block_from_words(P8),
        block_from_words(after_p8),
    ]);
    for block in &cases {
        assert_matches_core(block);
    }

    // Independent boundary expectations: ordinary reduces modulo P^8;
    // gamma computes (B mod (P^8-1)) + 1 before base-P decoding.
    assert_eq!(
        ordinary_sample(&block_from_words(P8_MINUS_ONE)).to_limbs(),
        [P - 1; 8]
    );
    assert_eq!(ordinary_sample(&block_from_words(P8)).to_limbs(), [0; 8]);
    assert_eq!(
        ordinary_sample(&block_from_words(after_p8)).to_limbs(),
        [1, 0, 0, 0, 0, 0, 0, 0]
    );
    assert_eq!(gamma_sample(&[0; 32]).to_limbs(), [1, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(
        gamma_sample(&block_from_words(P8_MINUS_ONE)).to_limbs(),
        [1, 0, 0, 0, 0, 0, 0, 0]
    );
    assert_eq!(
        gamma_sample(&block_from_words(P8)).to_limbs(),
        [2, 0, 0, 0, 0, 0, 0, 0]
    );
    assert_eq!(
        gamma_sample(&block_from_words(after_p8)).to_limbs(),
        [3, 0, 0, 0, 0, 0, 0, 0]
    );
    assert_eq!(
        gamma_sample(&block_from_words(p8_minus_two)).to_limbs(),
        [P - 1; 8]
    );
}

#[test]
fn optimized_samplers_match_frozen_core_on_deterministic_blocks() {
    // SplitMix64 is used only to produce a reproducible broad input set.
    // Exact equivalence is checked against the retained R0 implementation.
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    for _ in 0..4096 {
        let mut block = [0u8; 32];
        for chunk in block.chunks_exact_mut(8) {
            state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^= z >> 31;
            chunk.copy_from_slice(&z.to_le_bytes());
        }
        assert_matches_core(&block);
    }
}
