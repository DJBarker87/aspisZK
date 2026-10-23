//! Extraction-only reference forms. Never a prover or program dependency.
#[cfg(kani)]
#[path = "../../../crates/aspis-r1-cost-probe/src/transport.rs"]
mod shipped_transport;

/// D18's arithmetic digit permutation, on the admitted row domain 0..1024.
pub fn row_arithmetic(j: usize) -> usize {
    64 * (j % 4) + 256 * ((j / 4) % 4) + 16 * ((j / 16) % 4)
        + ((j / 64) % 4) + 4 * ((j / 256) % 4)
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn s2_row_equals_d18() {
    let j: usize = kani::any();
    kani::assume(j < 1024);
    let shipped = shipped_transport::Variant::S2.row(j);
    assert_eq!(shipped, row_arithmetic(j));
    assert!(shipped < 1024);
    assert_eq!(shipped_transport::Variant::S2.row(shipped), j);
}

#[cfg(kani)]
#[path = "../drop.rs"]
mod trace_drop;

#[cfg(kani)]
#[path = "../drop_iterator.rs"]
mod trace_drop_iterator;
