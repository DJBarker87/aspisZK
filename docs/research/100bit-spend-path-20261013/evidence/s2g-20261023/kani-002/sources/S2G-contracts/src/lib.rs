#![cfg(kani)]
#![allow(non_snake_case)]
// The two final parameters are ghost observations. Their preconditions must be
// established by the caller; they supply no assumption about the destination.
#[kani::requires(destination.len() == 1768 && source.len() == 1768)]
#[kani::requires(observed < 1768)]
#[kani::requires(expected == source[observed])]
#[kani::modifies(destination.as_mut_ptr().cast::<[u8;1768]>())]
#[kani::ensures(|_| destination[observed] == expected)]
pub fn S2G_copy(destination: &mut [u8], source: &[u8], observed: usize, expected: u8) {
    destination.copy_from_slice(source);
}

#[kani::proof_for_contract(S2G_copy)]
#[kani::unwind(1772)]
fn S2G_copy_contract() {
    let mut destination: [u8;1768] = kani::any();
    let source: [u8;1768] = kani::any();
    let observed: usize = kani::any();
    kani::assume(observed < 1768);
    S2G_copy(&mut destination, &source, observed, source[observed]);
    kani::cover!(observed == 0);
    kani::cover!(observed == 1767);
}

#[kani::proof]
#[kani::unwind(1772)]
#[kani::stub_verified(S2G_copy)]
fn S2G_copy_consumer() {
    let mut destination: [u8;1768] = kani::any();
    let source: [u8;1768] = kani::any();
    let protected: [u8;32] = kani::any();
    let before = protected;
    let observed: usize = kani::any();
    kani::assume(observed < 1768);
    let expected = source[observed];
    S2G_copy(&mut destination, &source, observed, expected);
    assert_eq!(destination[observed], expected);
    assert_eq!(source[observed], expected);
    assert_eq!(protected, before);
}
