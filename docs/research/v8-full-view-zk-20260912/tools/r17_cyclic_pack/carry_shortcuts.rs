// Uncompiled Rust integration leaves; exact arithmetic checked separately in C++.
// Use the same linked corelib type as the staged verifier.
use super::corelib::field::QM31 as K;

/// Replaces r17_owned_weights::xt_at, on its bounded PURE array reads.
/// Do not use this read-reordering identity on stateful/oracle callbacks.
#[inline]
pub(super) fn carry_at(read: impl Fn(usize) -> K, j: usize) -> K {
    assert!(j <= 1024);
    let mut bits = j.trailing_ones() as usize;
    let mut value = read(j + 1);
    while bits != 0 {
        bits -= 1;
        let row = j & !((1usize << (bits + 1)) - 1);
        value = value.add(read(row)).half();
    }
    value
}

/// Use inside the latest allocation-free Kernel::contract, retaining ALL 64
/// output groups and the actual source's zero extension at carry index 64.
#[inline]
pub(super) fn group_carry(read: impl Fn(usize) -> K, j: usize) -> K {
    assert!(j < 64);
    carry_at(|r| if r < 64 { read(r) } else { K::ZERO }, j)
}

/// Exact shortcut for Kernel::coordinate(1023). Slot 15 has no carry term.
/// This leaves the other coordinate cases and all image/query residuals alone.
#[inline]
pub(super) fn pivot_terminal(normal: &[K; 16], high: &[K; 16]) -> [K; 4] {
    let mut value = normal[15].mul(high[15]);
    for _ in 0..8 { value = value.half(); }
    [K::ZERO, K::ZERO, K::ZERO, value]
}
