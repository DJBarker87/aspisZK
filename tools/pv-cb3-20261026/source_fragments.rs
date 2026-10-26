//! Verbatim shipped expression/loop fragments; included only by cfg(kani).
//! Wrappers expose owned inputs and state outputs, not replacement callbacks.
use aspis_core::field::P;
pub fn words(block:&[u8;32])->[u32;8] {
    let mut quotient: [u32; 8] =
        core::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
    quotient
}
pub fn pass(rank:[u32;8])->([u32;8],u32) {
    let mut quotient=rank;
        let mut remainder = 0u64;
        for limb in quotient.iter_mut().rev() {
            let dividend = (remainder << 32) | u64::from(*limb);
            *limb = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }

    (quotient,remainder as u32)
}
pub fn carry(input:[u32;8],mut addend:u32)->([u32;8],bool) {
    let mut owned=input;
    let digits=&mut owned;
    for digit in digits {
        let sum = u64::from(*digit) + u64::from(addend);
        *digit = (sum % u64::from(P)) as u32;
        addend = (sum / u64::from(P)) as u32;
    }

    (owned,addend!=0)
}
