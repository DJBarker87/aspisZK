#![cfg(kani)]
#![allow(non_snake_case)]
// This is a byte-step contract, not a declaration that std::memcpy has been
// verified. Index and length are ghost coordinates; the selected native cells
// are valid references. The native slice/coordinate association is separate.
#[kani::requires(index < length)]
#[kani::requires(expected == *source)]
#[kani::modifies(destination)]
#[kani::ensures(|_| *destination == expected)]
pub fn S2W_copy_cell(destination: &mut u8, source: &u8,
    index: usize, length: usize, expected: u8) {
    *destination = *source;
}
#[kani::proof_for_contract(S2W_copy_cell)]
fn S2W_cell_contract() {
    let mut destination: u8 = kani::any();
    let source: u8 = kani::any();
    let index: usize = kani::any();
    let length: usize = kani::any();
    kani::assume(index < length);
    S2W_copy_cell(&mut destination, &source, index, length, source);
}
#[kani::proof]
#[kani::stub_verified(S2W_copy_cell)]
fn S2W_cell_consumer() {
    let mut destination: u8 = kani::any();
    let source: u8 = kani::any();
    let other_destination: u8 = kani::any();
    let before = other_destination;
    let index: usize = kani::any();
    kani::assume(index < 57607);
    let expected = source;
    S2W_copy_cell(&mut destination, &source, index, 57607, expected);
    assert!(destination == expected);
    assert!(source == expected);
    assert!(other_destination == before);
}
