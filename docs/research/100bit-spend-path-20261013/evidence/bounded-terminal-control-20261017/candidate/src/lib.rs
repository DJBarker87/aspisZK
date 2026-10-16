#![no_std]

/// The protocol only observes trailing ones below the 20-level tree bound.
/// This candidate replaces `(index.trailing_ones() as usize).min(20)` using
/// the same primitive operations already covered by the source proofs.
pub fn bounded_carry(mut index: u64) -> usize {
    let mut carry = 0usize;
    while carry < 20 {
        if index & 1 == 0 {
            return carry;
        }
        index >>= 1u32;
        carry += 1;
    }
    carry
}

/// Candidate explicit-match form of the existing public-amount guard.
pub fn invalid_amount(amount: Option<u32>) -> bool {
    match amount {
        None => false,
        Some(value) => value == 0 || value >= (1 << 30u32),
    }
}

#[cfg(test)]
mod tests {
    use super::{bounded_carry, invalid_amount};

    #[test]
    fn carry_matches_intrinsic_for_all_twenty_low_bits() {
        let low_mask = (1u64 << 20) - 1;
        let upper_patterns = [0, 1u64 << 20, 1u64 << 63, !low_mask];
        for low in 0..=low_mask {
            for upper in upper_patterns {
                let index = upper | low;
                assert_eq!(
                    bounded_carry(index),
                    (index.trailing_ones() as usize).min(20),
                    "index={index}"
                );
            }
        }
    }

    #[test]
    fn explicit_amount_guard_matches_option_method() {
        assert!(!invalid_amount(None));
        let boundaries = [0, 1, (1 << 30) - 1, 1 << 30, (1 << 31) - 1, u32::MAX];
        for value in boundaries {
            assert_eq!(invalid_amount(Some(value)), Some(value).is_some_and(|a| a == 0 || a >= (1 << 30)));
        }
        let mut state = 0x8f3a_92d1u32;
        for _ in 0..65536 {
            state ^= state << 13;
            state ^= state >> 17;
            state ^= state << 5;
            assert_eq!(invalid_amount(Some(state)), Some(state).is_some_and(|a| a == 0 || a >= (1 << 30)));
        }
    }
}
