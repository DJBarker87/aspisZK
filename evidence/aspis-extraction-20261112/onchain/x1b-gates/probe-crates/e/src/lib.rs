//! X1b item E reproducer: the frozen compile-time decoder (e0) and rewrites (e1, e2, e3).
pub mod e0 {
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
            carry >>= 8u32;
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

pub static A0: [u8; 32] = deployment_id(option_env!("ASPIS_R1_POOL_PROGRAM_ID"), [0x41; 32]);
}

/// e1: no early return inside a loop (an error code checked by the loop condition; the digit search and the
/// multiply-add in helpers); deployment_id unchanged.
pub mod e1 {
    const ALPHABET: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    /// The base58 digit of `c`, or 58 if `c` is not in the alphabet (the first match, as the frozen search).
    pub(crate) const fn base58_digit(c: u8) -> usize {
        let mut digit = 0;
        while digit < ALPHABET.len() && ALPHABET[digit] != c {
            digit += 1;
        }
        digit
    }
    /// `bytes * 58 + digit` over the big-endian 32-byte value, and the carry out of the top byte.
    pub(crate) const fn mul_add_58(mut bytes: [u8; 32], digit: u32) -> ([u8; 32], u32) {
        let mut carry = digit;
        let mut j = bytes.len();
        while j > 0 {
            j -= 1;
            carry += bytes[j] as u32 * 58;
            bytes[j] = carry as u8;
            carry >>= 8u32;
        }
        (bytes, carry)
    }
    pub(crate) const fn program_id(value: &str) -> Result<[u8; 32], &'static str> {
        let input = value.as_bytes();
        if input.is_empty() || input.len() > 44 {
            return Err("expected a base58 32-byte program id");
        }
        let mut bytes = [0u8; 32];
        // 0: no error; 1: invalid character; 2: more than 32 bytes. The loop stops at the first error, where the
        // frozen loop returned.
        let mut error = 0u8;
        let mut i = 0;
        while i < input.len() && error == 0 {
            let digit = base58_digit(input[i]);
            if digit == ALPHABET.len() {
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
    pub static A1: [u8; 32] = deployment_id(option_env!("ASPIS_R1_POOL_PROGRAM_ID"), [0x41; 32]);
}

/// e2: e1 with the failure branch of deployment_id as a panic with a fixed message (no formatting).
pub mod e2 {
    use super::e1::program_id;
    pub(crate) const fn deployment_id(value: Option<&str>, default: [u8; 32]) -> [u8; 32] {
        match value {
            None => default,
            Some(value) => match program_id(value) {
                Ok(bytes) => bytes,
                Err(_) => panic!("invalid deployment program id"),
            },
        }
    }
    pub static A2: [u8; 32] = deployment_id(option_env!("ASPIS_R1_POOL_PROGRAM_ID"), [0x41; 32]);
}

/// e3: e1 with the error carried as a `Result` to a separate checking step (no panic in the translated function).
pub mod e3 {
    use super::e1::program_id;
    pub(crate) const fn deployment_id_result(value: Option<&str>, default: [u8; 32]) -> Result<[u8; 32], &'static str> {
        match value {
            None => Ok(default),
            Some(value) => program_id(value),
        }
    }
    pub(crate) const fn unwrap_id(r: Result<[u8; 32], &'static str>) -> [u8; 32] {
        match r {
            Ok(bytes) => bytes,
            Err(_) => panic!("invalid deployment program id"),
        }
    }
    pub static A3: [u8; 32] = unwrap_id(deployment_id_result(option_env!("ASPIS_R1_POOL_PROGRAM_ID"), [0x41; 32]));
}

/// e4: a constant item evaluated by the compiler, referenced by the static.
pub mod e4 {
    use super::e1::deployment_id;
    const V: [u8; 32] = deployment_id(option_env!("ASPIS_R1_POOL_PROGRAM_ID"), [0x41; 32]);
    pub static A4: [u8; 32] = V;
}

/// e5: e1 with the scans as `while` loops ending by `break` (no index in a loop condition), fixed-message panic.
pub mod e5 {
    const ALPHABET: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    pub(crate) const fn base58_digit(c: u8) -> usize {
        let mut digit = 0;
        while digit < 58 {
            if ALPHABET[digit] == c {
                break;
            }
            digit += 1;
        }
        digit
    }
    pub(crate) const fn leading_ones(input: &[u8]) -> usize {
        let mut k = 0;
        while k < input.len() {
            if input[k] != b'1' {
                break;
            }
            k += 1;
        }
        k
    }
    pub(crate) const fn leading_zeros(bytes: [u8; 32]) -> usize {
        let mut k = 0;
        while k < 32 {
            if bytes[k] != 0 {
                break;
            }
            k += 1;
        }
        k
    }
    include!("common.rs");
    pub static A5: [u8; 32] = deployment_id(option_env!("ASPIS_R1_POOL_PROGRAM_ID"), [0x41; 32]);
}

/// e6: no loop over the alphabet (the digit of a base58 character by its ASCII range; the alphabet omits 0, I, O, l);
/// the scans as `while` loops with a flag in the condition.
pub mod e6 {
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
    pub(crate) const fn leading_ones(input: &[u8]) -> usize {
        let mut k = 0;
        let mut go = true;
        while go && k < input.len() {
            if input[k] == b'1' { k += 1; } else { go = false; }
        }
        k
    }
    pub(crate) const fn leading_zeros(bytes: [u8; 32]) -> usize {
        let mut k = 0;
        let mut go = true;
        while go && k < 32 {
            if bytes[k] == 0 { k += 1; } else { go = false; }
        }
        k
    }
    include!("common.rs");
    pub static A6: [u8; 32] = deployment_id(option_env!("ASPIS_R1_POOL_PROGRAM_ID"), [0x41; 32]);
}
