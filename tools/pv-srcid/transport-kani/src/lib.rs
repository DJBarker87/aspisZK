//! Source-only validation of the actual coefficient-array wrapper.
//! No shipped crate depends on this crate; no function stubs.
#[cfg(kani)]
#[path = "../../../../crates/aspis-r1-cost-probe/src/transport.rs"]
mod shipped;

/// Match the shipped QM31 coefficient cell's four-word copy carrier.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_coefficients_cell() {
    let rows: [[u32; 4]; 1024] = kani::any();
    let j: usize = kani::any();
    kani::assume(j < 1024);
    let coefficients = shipped::Variant::S2.coefficients(&rows);
    assert_eq!(coefficients[j], rows[aspis_r1_builder_reference::row_arithmetic(j)]);
}

/// Exercise the shipped QM31 carrier, including noncanonical raw M31 words.
/// The wrapper only copies cells, so no field-arithmetic precondition is needed.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_coefficients_cell() {
    use aspis_core::field::{CM31, M31, QM31};
    let words: [[u32; 4]; 1024] = kani::any();
    let rows: [QM31; 1024] = core::array::from_fn(|i| QM31 {
        c0: CM31 { a: M31(words[i][0]), b: M31(words[i][1]) },
        c1: CM31 { a: M31(words[i][2]), b: M31(words[i][3]) },
    });
    let j: usize = kani::any();
    kani::assume(j < 1024);
    let coefficients = shipped::Variant::S2.coefficients(&rows);
    assert_eq!(coefficients[j], rows[aspis_r1_builder_reference::row_arithmetic(j)]);
}
