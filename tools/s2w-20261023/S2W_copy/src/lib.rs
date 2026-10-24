#![cfg(kani)]
#![allow(non_snake_case)]
// The two final parameters are ghost observations. Their preconditions must be
// established by the caller; they supply no assumption about the destination.
#[kani::requires(destination.len() == 57607 && source.len() == 57607)]
#[kani::requires(observed < 57607)]
#[kani::requires(expected == source[observed])]
#[kani::modifies(destination.as_mut_ptr().cast::<[u8;57607]>())]
#[kani::ensures(|_| destination[observed] == expected)]
pub fn S2W_copy(destination: &mut [u8], source: &[u8], observed: usize, expected: u8) {
    destination.copy_from_slice(source);
}

#[kani::proof_for_contract(S2W_copy)]
#[kani::unwind(57611)]
fn S2W_copy_contract() {
    let mut destination: [u8;57607] = kani::any();
    let source: [u8;57607] = kani::any();
    let observed: usize = kani::any();
    kani::assume(observed < 57607);
    S2W_copy(&mut destination, &source, observed, source[observed]);
    kani::cover!(observed == 0);
    kani::cover!(observed == 57606);
}

#[kani::proof]
#[kani::unwind(57611)]
#[kani::stub_verified(S2W_copy)]
fn S2W_copy_consumer() {
    let mut destination: [u8;57607] = kani::any();
    let source: [u8;57607] = kani::any();
    let protected: [u8;32] = kani::any();
    let before = protected;
    let observed: usize = kani::any();
    kani::assume(observed < 57607);
    let expected = source[observed];
    S2W_copy(&mut destination, &source, observed, expected);
    assert_eq!(destination[observed], expected);
    assert_eq!(source[observed], expected);
    assert_eq!(protected, before);
}
