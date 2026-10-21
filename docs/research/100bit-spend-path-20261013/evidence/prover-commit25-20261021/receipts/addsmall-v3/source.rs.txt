const P: u32 = 2147483647;
mod shipped { use super::P;
pub fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
    for digit in digits {
        let sum = u64::from(*digit) + u64::from(addend);
        *digit = (sum % u64::from(P)) as u32;
        addend = (sum / u64::from(P)) as u32;
    }
    debug_assert!(addend <= 1);
    addend != 0
}
}
mod reference { use super::P;
pub fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
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
}

#[kani::proof]
#[kani::unwind(10)]
fn iterator_equals_indexed() {
    let digits: [u32; 8] = kani::any();
    let addend: u32 = kani::any();
    for digit in digits { kani::assume(digit < P); }
    kani::assume(addend <= 257);
    let mut left = digits;
    let mut right = digits;
    let a = shipped::add_small_base_p(&mut left, addend);
    let b = reference::add_small_base_p(&mut right, addend);
    assert_eq!(a, b);
    for i in 0..8 { assert_eq!(left[i], right[i]); }
}
