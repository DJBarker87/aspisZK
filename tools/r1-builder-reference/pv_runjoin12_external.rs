//! Unstubbed whole external-layer equality, over all raw machine-word states.
//! The parent module exists only in cfg(kani)/cfg(aeneas_ref) builds; this
//! child is additionally cfg(kani). No source callee is replaced.
use super::*;
#[kani::proof]
#[kani::unwind(33)]
fn external_all_words() {
    let input = kani::any::<[u32;16]>().map(M31);
    let mut actual = input;
    external_linear_lazy(&mut actual);
    let expected = external_owned(input);
    assert_eq!(actual, expected);
}
