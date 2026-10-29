//! Prover-local Drop-free samplers (D187 batch 2).
use aspis_core::field::{WideExact,P};
fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
    let mut quotient = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        quotient[i] = (block[4*i] as u32) | ((block[4*i+1] as u32)<<8u32) | ((block[4*i+2] as u32)<<16u32) | ((block[4*i+3] as u32)<<24u32);
        i += 1;
    }
    let mut digits = [0u32; 8];
    let mut d = 0usize;
    while d < 8 {
        let mut remainder = 0u64;
        let mut j = 8usize;
        while j > 0 {
            j -= 1;
            let dividend = (remainder << 32u32) | u64::from(quotient[j]);
            quotient[j] = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }
        digits[d] = remainder as u32;
        d += 1;
    }

    // After eight divisions, the quotient is at most 256 and fits in u32.
    let mut check = 1usize;
    while check < 8 { debug_assert!(quotient[check] == 0); check += 1; }
    debug_assert!(quotient[0] <= 256);
    (digits, quotient[0])
}

fn decode8(digits: [u32; 8]) -> WideExact {
    WideExact::from_limbs(digits).unwrap()
}

/// Add a small integer to a base-P digit vector. Returns the carry beyond
/// the final digit, which is at most one for the values used by the sampler.
fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
    let mut i = 0usize;
    while i < 8 {
        let sum = u64::from(digits[i]) + u64::from(addend);
        digits[i] = (sum % u64::from(P)) as u32;
        addend = (sum / u64::from(P)) as u32;
        i += 1;
    }
    debug_assert!(addend <= 1);
    addend != 0
}

/// `decode8(rank(block) mod P^8)`, byte-for-byte equivalent to the frozen
/// R0 sampler. The repeated divisions directly produce the low eight digits.
pub fn ordinary_sample(block: &[u8; 32]) -> WideExact {
    let (digits, _) = low_base_p_digits(block);
    decode8(digits)
}

/// `decode8((rank(block) mod (P^8 - 1)) + 1)`, byte-for-byte equivalent to
/// the frozen R0 sampler. Since `P^8 ≡ 1 (mod P^8 - 1)`, the high quotient can
/// be added to the low digits before the final increment. A carry past digit
/// seven contributes one more modulo `P^8 - 1`.
pub fn gamma_sample(block: &[u8; 32]) -> WideExact {
    let (mut digits, quotient) = low_base_p_digits(block);
    let wrapped = add_small_base_p(&mut digits, quotient + 1);
    if wrapped {
        let wrapped_again = add_small_base_p(&mut digits, 1);
        debug_assert!(!wrapped_again);
    }
    decode8(digits)
}


pub fn low_for_audit(b:&[u8;32])->([u32;8],u32){low_base_p_digits(b)}
pub fn add_for_audit(mut ds:[u32;8],n:u32)->(bool,[u32;8]){let wrapped=add_small_base_p(&mut ds,n);(wrapped,ds)}
