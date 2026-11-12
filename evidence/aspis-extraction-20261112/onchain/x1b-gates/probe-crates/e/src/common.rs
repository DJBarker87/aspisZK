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
pub(crate) const fn program_id(value: &str) -> Result<[u8; 32], &'static str> {
    let input = value.as_bytes();
    let n = input.len();
    if n == 0 || n > 44 {
        return Err("expected a base58 32-byte program id");
    }
    let mut bytes = [0u8; 32];
    // 0: no error; 1: invalid character; 2: more than 32 bytes. The loop stops at the first error.
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
            Err(_) => panic!("invalid deployment program id"),
        },
    }
}
