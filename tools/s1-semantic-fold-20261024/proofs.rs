//! Normal-return control equivalence. Child arithmetic is a common arbitrary
//! full-QM31 tape, not a numeric correctness or abort-totality assumption.
use super::{native, reference, QM31};
use aspis_core::field::{M31, CM31};

static mut POLY: [[u32; 4]; 28] = [[0; 4]; 28];
static mut ALPHA: [[u32; 4]; 10] = [[0; 4]; 10];
static mut TAPE: [[u32; 4]; 56] = [[0; 4]; 56];
static mut CALLS: usize = 0;
static mut VALUE: bool = false;
static mut ROUND: usize = 0;

fn q(w: [u32; 4]) -> QM31 {
    QM31 { c0: CM31 { a: M31(w[0]), b: M31(w[1]) },
           c1: CM31 { a: M31(w[2]), b: M31(w[3]) } }
}
fn words(x: QM31) -> [u32; 4] {
    [x.c0.a.0, x.c0.b.0, x.c1.a.0, x.c1.b.0]
}
fn same(a: [u32; 4], b: [u32; 4]) -> bool {
    (a[0] == b[0]) & (a[1] == b[1]) &
    (a[2] == b[2]) & (a[3] == b[3])
}
fn add_leaf(a: QM31, b: QM31) -> QM31 { unsafe {
    let n = CALLS;
    if VALUE {
        assert!(n < 56);
        assert_eq!(n % 2, 1);
        assert!(same(words(a), TAPE[n - 1]));
        assert!(same(words(b), POLY[27 - n / 2]));
    } else {
        assert!(n < 28);
        assert!(same(words(a), if n == 0 { POLY[0] } else { TAPE[n - 1] }));
        assert!(same(words(b), POLY[n]));
    }
    CALLS = n + 1;
    q(TAPE[n])
} }
fn mul_leaf(a: QM31, b: QM31) -> QM31 { unsafe {
    let n = CALLS;
    assert!(VALUE);
    assert!(n < 56);
    assert_eq!(n % 2, 0);
    assert!(same(words(a), if n == 0 { [0; 4] } else { TAPE[n - 1] }));
    assert!(same(words(b), ALPHA[ROUND]));
    CALLS = n + 1;
    q(TAPE[n])
} }
fn inputs() -> ([QM31; 28], [QM31; 10]) { unsafe {
    POLY = kani::any(); ALPHA = kani::any(); TAPE = kani::any();
    let mut p = [QM31::ZERO; 28];
    let mut a = [QM31::ZERO; 10];
    let mut i = 0;
    while i < 28 { p[i] = q(POLY[i]); i += 1; }
    i = 0;
    while i < 10 { a[i] = q(ALPHA[i]); i += 1; }
    (p, a)
} }

#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(aspis_core::field::QM31::add, add_leaf)]
#[kani::stub(aspis_core::field::QM31::mul, mul_leaf)]
fn boundary_same_complete_calls() {
    let (p, _) = inputs();
    unsafe { VALUE = false; CALLS = 0; }
    let a = native::semantic_boundary(&p);
    unsafe { assert_eq!(CALLS, 28); assert!(same(words(a), TAPE[27])); CALLS = 0; }
    let b = reference::semantic_boundary(&p);
    unsafe { assert_eq!(CALLS, 28); assert!(same(words(b), TAPE[27])); }
    assert!(same(words(a), words(b)));
}

#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(aspis_core::field::QM31::add, add_leaf)]
#[kani::stub(aspis_core::field::QM31::mul, mul_leaf)]
fn value_same_complete_calls() {
    let (p, a) = inputs();
    let round = kani::any::<u8>() as usize;
    kani::assume(round < 10);
    unsafe { VALUE = true; ROUND = round; CALLS = 0; }
    let x = native::semantic_value(&p, &a, round);
    unsafe { assert_eq!(CALLS, 56); assert!(same(words(x), TAPE[55])); CALLS = 0; }
    let y = reference::semantic_value(&p, &a, round);
    unsafe { assert_eq!(CALLS, 56); assert!(same(words(y), TAPE[55])); }
    assert!(same(words(x), words(y)));
}
