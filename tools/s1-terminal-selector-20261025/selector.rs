use aspis_core::field::{QM31,CM31,M31};
fn native_selector(claims:&[[QM31;29];3])->[QM31;84]{core::array::from_fn(|i| claims[i / 28][i % 28])}
#[inline(always)]
pub(crate) fn array_from_fn_copy<T: Copy, const N: usize>(
    init: T,
    mut f: impl FnMut(usize) -> T,
) -> [T; N] {
    let mut out = [init; N];
    let mut i = 0usize;
    while i < N {
        out[i] = f(i);
        i += 1;
    }
    out
}
fn copy_selector(claims:&[[QM31;29];3])->[QM31;84]{array_from_fn_copy::<_,84>(QM31::ZERO,|i| claims[i / 28][i % 28])}
#[cfg(kani)]
#[path="terminal_selector_proofs.rs"]mod proofs;
