use aspis_core::field::{WideExact, CM31, M31, P, QM31};
fn qm31_div_pass(mut rank: [u32; 8]) -> ([u32; 8], u32) {
    let mut remainder = 0u64;
    let mut j = 8usize;
    while j > 0 {
        j -= 1;
        let dividend = (remainder << 32) | u64::from(rank[j]);
        rank[j] = (dividend / u64::from(P)) as u32;
        remainder = dividend % u64::from(P);
    }
    (rank, remainder as u32)
}
fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
    let mut rank = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        let start = 4 * i;
        rank[i] = u32::from_le_bytes([
            block[start],
            block[start + 1],
            block[start + 2],
            block[start + 3],
        ]);
        i += 1;
    }

    let mut digits = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        let (quotient, digit) = qm31_div_pass(rank);
        rank = quotient;
        digits[i] = digit;
        i += 1;
    }
    (digits, rank[0])
}
fn decode8(digits: [u32; 8]) -> WideExact {
    WideExact::new(
        QM31 {
            c0: CM31::new(M31(digits[0]), M31(digits[1])),
            c1: CM31::new(M31(digits[2]), M31(digits[3])),
        },
        QM31 {
            c0: CM31::new(M31(digits[4]), M31(digits[5])),
            c1: CM31::new(M31(digits[6]), M31(digits[7])),
        },
    )
}
fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
    let mut i: usize = 0;
    while i < 8 {
        let sum = u64::from(digits[i]) + u64::from(addend);
        digits[i] = (sum % u64::from(P)) as u32;
        addend = (sum / u64::from(P)) as u32;
        i += 1;
    }
    debug_assert!(addend <= 1);
    addend != 0
}
pub fn ordinary_sample(block: &[u8; 32]) -> WideExact {
    let (digits, _) = low_base_p_digits(block);
    decode8(digits)
}
pub fn gamma_sample(block: &[u8; 32]) -> WideExact {
    let (mut digits, quotient) = low_base_p_digits(block);
    let wrapped = add_small_base_p(&mut digits, quotient + 1);
    if wrapped {
        let wrapped_again = add_small_base_p(&mut digits, 1);
        debug_assert!(!wrapped_again);
    }
    decode8(digits)
}
