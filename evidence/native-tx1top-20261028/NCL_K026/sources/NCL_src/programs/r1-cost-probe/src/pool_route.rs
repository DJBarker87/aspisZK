//! The complete instruction surface admitted by the Pool release build.

pub(super) fn admitted(data: &[u8]) -> bool {
    data == [3, 10] || data == [3, 11] || data.starts_with(b"ASQ8")
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
        for tag in [1, 2, 4, 5, 6] {
            for tail in [&[][..], &[0], &[10, 11], b"ASQ8", &[255; 256]] {
                let mut data = vec![tag];
                data.extend_from_slice(tail);
                assert!(!admitted(&data));
            }
        }
    }
}
