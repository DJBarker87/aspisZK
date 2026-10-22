const P: u32 = 2147483647;
mod shipped { use super::P;
pub fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
    let mut quotient: [u32; 8] =
        core::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
    let digits = core::array::from_fn(|_| {
        let mut remainder = 0u64;
        for limb in quotient.iter_mut().rev() {
            let dividend = (remainder << 32) | u64::from(*limb);
            *limb = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }
        remainder as u32
    });

    // After eight divisions, the quotient is at most 256 and fits in u32.
    debug_assert!(quotient[1..].iter().all(|&limb| limb == 0));
    debug_assert!(quotient[0] <= 256);
    (digits, quotient[0])
}
}
mod reference { use super::P;
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
pub fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
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
}
#[kani::proof]
#[kani::unwind(12)]
fn low_iterator_equals_indexed() {
 let block: [u8;32] = kani::any();
 let (left,qleft) = shipped::low_base_p_digits(&block);
 let (right,qright) = reference::low_base_p_digits(&block);
 assert_eq!(qleft,qright);
 for i in 0..8 { assert_eq!(left[i],right[i]); }
}
