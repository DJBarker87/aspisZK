//! Compile-time deployment addresses. No decoder is called by the program.
//!
//! The decoder written so that the translator takes it (no early return inside a loop, no index in a
//! loop condition, no formatted panic): the base58 digit by ASCII range, the decoding loop stopped by an error code,
//! the leading-character scans as loops with a flag. Same result for every input; only the compile-time panic
//! message of `deployment_id` is a fixed text (the decoder's own message is in `program_id`'s error value).

/// The base58 digit of `c` (alphabet `1-9 A-H J-N P-Z a-k m-z`), or 58 if `c` is not a base58 character.
pub(crate) const fn base58_digit(c: u8) -> usize {
    match c {
        b'1'..=b'9' => (c - b'1') as usize,
        b'A'..=b'H' => (c - b'A') as usize + 9,
        b'J'..=b'N' => (c - b'J') as usize + 17,
        b'P'..=b'Z' => (c - b'P') as usize + 22,
        b'a'..=b'k' => (c - b'a') as usize + 33,
        b'm'..=b'z' => (c - b'm') as usize + 44,
        _ => 58,
    }
}

/// `bytes * 58 + digit` over the big-endian 32-byte value, and the carry out of the top byte.
pub(crate) const fn mul_add_58(mut bytes: [u8; 32], digit: u32) -> ([u8; 32], u32) {
    let mut carry = digit;
    let mut j = 32;
    while j > 0 {
        j -= 1;
        carry += bytes[j] as u32 * 58;
        bytes[j] = carry as u8;
        carry >>= 8u32;
    }
    (bytes, carry)
}

/// The number of leading `b'1'` characters of `input`.
pub(crate) const fn leading_ones(input: &[u8]) -> usize {
    let mut k = 0;
    let mut go = true;
    while go && k < input.len() {
        if input[k] == b'1' { k += 1; } else { go = false; }
    }
    k
}

/// The number of leading zero bytes of `bytes`.
pub(crate) const fn leading_zeros(bytes: [u8; 32]) -> usize {
    let mut k = 0;
    let mut go = true;
    while go && k < 32 {
        if bytes[k] == 0 { k += 1; } else { go = false; }
    }
    k
}

pub(crate) const fn program_id(value: &str) -> Result<[u8; 32], &'static str> {
    let input = value.as_bytes();
    let n = input.len();
    if n == 0 || n > 44 {
        return Err("expected a base58 32-byte program id");
    }
    let mut bytes = [0u8; 32];
    // 0: no error; 1: invalid character; 2: more than 32 bytes. The loop stops at the first error, at the character
    // where the frozen loop returned.
    let mut error = 0u8;
    let mut i = 0;
    while error == 0 && i < n {
        let digit = base58_digit(input[i]);
        if digit == 58 {
            error = 1;
        } else {
            let (next, carry) = mul_add_58(bytes, digit as u32);
            bytes = next;
            if carry != 0 {
                error = 2;
            }
        }
        i += 1;
    }
    if error == 1 {
        return Err("invalid base58 character");
    }
    if error == 2 {
        return Err("program id exceeds 32 bytes");
    }
    if leading_ones(input) != leading_zeros(bytes) {
        return Err("program id must decode to exactly 32 bytes");
    }
    Ok(bytes)
}

pub(crate) const fn deployment_id(value: Option<&str>, default: [u8; 32]) -> [u8; 32] {
    match value {
        None => default,
        Some(value) => match program_id(value) {
            Ok(bytes) => bytes,
            Err(_) => panic!("ASPIS_R1_*_PROGRAM_ID is not a base58 32-byte program id"),
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

/// Differential test of the rewritten decoder against the frozen one (deployment_ids.rs 3-55), on the
/// two deployment ids, every single base58 character string up to length 3, edge lengths, and random strings over the
/// alphabet plus invalid characters.
#[cfg(test)]
mod decoder_loop_form {
    extern crate std;
    mod frozen {
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
    }

    #[test]
    fn digit_table_matches_the_alphabet_search() {
        let alphabet = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
        for c in 0..=255u8 {
            assert_eq!(super::base58_digit(c), alphabet.iter().position(|a| *a == c).unwrap_or(58), "{c}");
        }
    }

    #[test]
    fn same_result_as_the_frozen_decoder() {
        let alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz0OIl+ ";
        let chars: std::vec::Vec<char> = alphabet.chars().collect();
        let mut inputs: std::vec::Vec<std::string::String> = std::vec![
            "4hxEyoU8MC3oFMya8D8MAcvhCPhLfHKDP1Ji9byYycn1".into(), "9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q".into(),
            "37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt".into(), "11111111111111111111111111111111".into(),
            "".into(), "1".repeat(44), "1".repeat(45), "z".repeat(44), "z".repeat(43), "2".repeat(44)];
        for a in &chars { inputs.push(a.to_string()); for b in &chars { inputs.push(std::format!("{a}{b}")); } }
        let mut s = 31u64;
        for _ in 0..20_000 {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let n = (s >> 33) as usize % 47;
            let mut t = std::string::String::new();
            for _ in 0..n { s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); let k = (s >> 33) as usize % if n % 5 == 0 { chars.len() } else { 58 }; t.push(chars[k]); }
            inputs.push(t);
        }
        let mut ok = 0;
        for t in &inputs {
            let r = super::program_id(t);
            if r.is_ok() { ok += 1; }
            assert_eq!(r, frozen::program_id(t), "{t}");
        }
        assert!(ok > 100);
        assert_eq!(super::deployment_id(None, [3; 32]), frozen::deployment_id(None, [3; 32]));
        assert_eq!(super::deployment_id(Some(&inputs[0]), [3; 32]), frozen::deployment_id(Some(&inputs[0]), [3; 32]));
    }
}
