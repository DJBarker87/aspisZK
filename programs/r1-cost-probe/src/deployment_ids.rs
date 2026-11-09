//! Compile-time deployment addresses. No decoder is called by the program.

pub(crate) const fn program_id(value: &str) -> Result<[u8; 32], &'static str> {
    const ALPHABET: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    let input = value.as_bytes();
    if input.is_empty() || input.len() > 44 {
        return Err("expected a base58 32-byte program id");
    }
    let mut bytes = [0u8; 32];
    let mut i = 0;
    while i < input.len() {
        let mut digit = 0;
        while digit < ALPHABET.len() && ALPHABET[digit] != input[i] {
            digit += 1;
        }
        if digit == ALPHABET.len() {
            return Err("invalid base58 character");
        }
        let mut carry = digit as u32;
        let mut j = bytes.len();
        while j > 0 {
            j -= 1;
            carry += bytes[j] as u32 * 58;
            bytes[j] = carry as u8;
            carry >>= 8;
        }
        if carry != 0 {
            return Err("program id exceeds 32 bytes");
        }
        i += 1;
    }
    let mut leading_ones = 0;
    while leading_ones < input.len() && input[leading_ones] == b'1' {
        leading_ones += 1;
    }
    let mut leading_zeros = 0;
    while leading_zeros < bytes.len() && bytes[leading_zeros] == 0 {
        leading_zeros += 1;
    }
    if leading_ones != leading_zeros {
        return Err("program id must decode to exactly 32 bytes");
    }
    Ok(bytes)
}

pub(crate) const fn deployment_id(value: Option<&str>, default: [u8; 32]) -> [u8; 32] {
    match value {
        None => default,
        Some(value) => match program_id(value) {
            Ok(bytes) => bytes,
            Err(error) => panic!("{}", error),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::{deployment_id, program_id};

    #[test]
    fn canonical_addresses_and_invalid_inputs() {
        const DEFAULT: [u8; 32] = deployment_id(None, [0x41; 32]);
        const ZERO: [u8; 32] = deployment_id(Some("11111111111111111111111111111111"), [1; 32]);
        assert_eq!(DEFAULT, [0x41; 32]);
        assert_eq!(ZERO, [0; 32]);
        assert_eq!(
            program_id("5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx"),
            Ok([0x41; 32])
        );
        assert_eq!(
            program_id("5bV6jUfhDHCQVA1WfKBUnXUsboJgoKgkzkKcxr3joew5"),
            Ok([0x44; 32])
        );
        for invalid in [
            "",
            "0",
            "111",
            "111111111111111111111111111111111",
            "zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz",
        ] {
            assert!(program_id(invalid).is_err(), "{invalid}");
        }
    }
}
