//! Research-only replacement of a bytewise all-zero predicate.
//! No alignment, canonicality, provenance or honest-account premise.
#[inline]
pub fn all_zero(bytes: &[u8]) -> bool {
    let mut chunks = bytes.chunks_exact(8);
    for chunk in &mut chunks {
        // chunks_exact proves this conversion cannot fail. LE is immaterial
        // for zero detection, but pins the integer model in ZeroPage.lean.
        let word = u64::from_le_bytes(chunk.try_into().expect("exact eight-byte chunk"));
        if word != 0 {
            return false;
        }
    }
    chunks.remainder().iter().all(|byte| *byte == 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn each_nonzero_value_at_every_page_position() {
        let mut page = [0u8; 8256];
        assert!(all_zero(&page));
        for index in 0..page.len() {
            for value in 1..=255 {
                page[index] = value;
                assert!(!all_zero(&page), "index={index}, value={value}");
            }
            page[index] = 0;
        }
    }

    #[test]
    fn offsets_short_lengths_and_remainders() {
        let mut backing = [0u8; 81];
        for offset in 0..8 {
            for len in 0..=64 {
                assert!(all_zero(&backing[offset..offset + len]));
                for index in offset..offset + len {
                    backing[index] = 128;
                    assert!(!all_zero(&backing[offset..offset + len]));
                    backing[index] = 0;
                }
            }
        }
    }

    #[test]
    fn deterministic_multibyte_reference_comparison() {
        let mut seed = 0x6368756e6b5f7631u64;
        let mut backing = [0u8; 8256 + 8];
        for trial in 0..4096 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            let len = (seed as usize) % 8257;
            let offset = trial % 8;
            backing.fill(0);
            if trial % 3 != 0 {
                for index in (0..len).step_by(1 + trial % 257) {
                    backing[offset + index] = (seed >> (index % 8 * 8)) as u8;
                }
            }
            let bytes = &backing[offset..offset + len];
            assert_eq!(all_zero(bytes), bytes.iter().all(|b| *b == 0));
        }
    }
}
