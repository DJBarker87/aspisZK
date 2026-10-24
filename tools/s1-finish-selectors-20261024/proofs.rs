use super::{native, reference, QM31};
use aspis_core::field::{M31, CM31};
fn q(w: [u32; 4]) -> QM31 {
    QM31 { c0: CM31 { a: M31(w[0]), b: M31(w[1]) },
           c1: CM31 { a: M31(w[2]), b: M31(w[3]) } }
}
fn same(a: QM31, b: QM31) -> bool {
    (a.c0.a.0 == b.c0.a.0) & (a.c0.b.0 == b.c0.b.0) &
    (a.c1.a.0 == b.c1.a.0) & (a.c1.b.0 == b.c1.b.0)
}
#[kani::proof]
#[kani::unwind(64)]
fn finish_selectors_match_full_words() {
    let words: [[[u32; 4]; 29]; 3] = kani::any();
    let mut input = [[QM31::ZERO; 29]; 3];
    let mut p = 0;
    while p < 3 {
        let mut i = 0;
        while i < 29 { input[p][i] = q(words[p][i]); i += 1; }
        p += 1;
    }
    // Input allocation is harness setup, not a proof of claims() allocation.
    let claims = Box::new(input);
    let (first, second) = native(&claims);
    let (first_ref, second_ref) = reference(&input);
    let mut i = 0;
    while i < 16 {
        assert!(same(first[i], first_ref[i]));
        assert!(same(first[i], input[0][i]));
        i += 1;
    }
    i = 0;
    while i < 10 {
        assert!(same(second[i], second_ref[i]));
        assert!(same(second[i], input[0][16 + i]));
        i += 1;
    }
    // Both source and reference borrow their inputs immutably.
    assert!(!core::mem::needs_drop::<QM31>());
}
