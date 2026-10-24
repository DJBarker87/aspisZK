use aspis_core::field::QM31;

// Selected expressions from the native verify_finish call site. The input is
// the complete borrowed Box, preserving the shipped carrier's dereference.
fn native(claims: &Box<[[QM31; 29]; 3]>) -> ([QM31; 16], [QM31; 10]) {
    (core::array::from_fn(|i| claims[0][i]),
     core::array::from_fn(|i| claims[0][16 + i]))
}
fn reference(claims: &[[QM31; 29]; 3]) -> ([QM31; 16], [QM31; 10]) {
    let mut first = [QM31::ZERO; 16];
    let mut second = [QM31::ZERO; 10];
    let mut i = 0;
    while i < 16 { first[i] = claims[0][i]; i += 1; }
    i = 0;
    while i < 10 { second[i] = claims[0][16 + i]; i += 1; }
    (first, second)
}
#[cfg(kani)] mod proofs;
