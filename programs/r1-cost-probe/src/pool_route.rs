//! The complete instruction surface admitted by the Pool release build.

/// Instruction tag of the verifier checkpoint close, `[7, seed_len, seed...]`.
/// Tag 6 is not used: the adapter dispatch binds it to the legacy lifecycle
/// finalizer, which this guard keeps unreachable.
pub(super) const CLOSE_CHECKPOINT_TAG: u8 = 7;

/// `[7, seed_len, seed...]` with `seed_len == seed.len()` and `1..=32` bytes.
pub(super) fn is_close_checkpoint(data: &[u8]) -> bool {
    data.len() >= 3
        && data[0] == CLOSE_CHECKPOINT_TAG
        && data[1] as usize == data.len() - 2
        && 1 <= data[1] && data[1] <= 32
}

pub(super) fn admitted(data: &[u8]) -> bool {
    data == [3, 10] || data == [3, 11] || data.starts_with(b"ASQ8") || is_close_checkpoint(data)
}

#[cfg(test)]
mod tests {
    use super::admitted;

    #[test]
    fn only_stage1_and_asq8_are_admitted() {
        assert!(admitted(&[3, 10]));
        assert!(admitted(&[3, 11]));
        assert!(admitted(b"ASQ8"));
        assert!(admitted(b"ASQ8\x00\xff"));
        assert!(!admitted(&[]));
        for a in 0..=u8::MAX {
            assert!(!admitted(&[a]));
            for b in 0..=u8::MAX {
                assert_eq!(admitted(&[a, b]), a == 3 && (b == 10 || b == 11));
            }
        }
        for data in [&[3, 10, 0][..], &[3, 11, 0], b"ASQ", b"ASQ9", b"XASQ8"] {
            assert!(!admitted(data));
        }
    }

    #[test]
    fn lifecycle_and_legacy_prefixes_are_rejected() {
        for tag in [1, 2, 4, 5, 6, 7] {
            for tail in [&[][..], &[0], &[10, 11], b"ASQ8", &[255; 256]] {
                let mut data = vec![tag];
                data.extend_from_slice(tail);
                assert!(!admitted(&data));
            }
        }
    }

    #[test]
    fn close_checkpoint_admits_exactly_well_formed_seed_lengths() {
        // Every tag, every declared length 0..=255 and every actual seed
        // length 0..=40: admitted iff tag 7, declared == actual, 1..=32.
        for tag in 0..=u8::MAX {
            for declared in 0..=u8::MAX {
                for actual in 0..=40usize {
                    let mut data = vec![tag, declared];
                    data.extend(core::iter::repeat(b'a').take(actual));
                    let expected = tag == 7 && declared as usize == actual && (1..=32).contains(&actual);
                    // Unrelated admitted forms that this loop can construct.
                    let other = data == [3, 10] || data == [3, 11] || data.starts_with(b"ASQ8");
                    assert_eq!(admitted(&data), expected || other, "{tag} {declared} {actual}");
                }
            }
        }
        assert!(admitted(&[7, 1, b'x']));
        assert!(admitted(&[&[7u8, 32][..], &[b'z'; 32]].concat()));
        assert!(!admitted(&[&[7u8, 33][..], &[b'z'; 33]].concat()));
        assert!(!admitted(&[7, 0]));
        assert!(!admitted(&[7, 2, b'x']));
        assert!(!admitted(&[7, 1, b'x', b'y']));
        // The tag-6 lifecycle finalizer stays outside the surface in this form.
        assert!(!admitted(&[6, 1, b'x']));
    }
}
