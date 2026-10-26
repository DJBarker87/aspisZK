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
