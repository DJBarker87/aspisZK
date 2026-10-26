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

/// Actual unmasked builder carrier, one arbitrary raw M31 word per cell.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_m31_coefficients_cell() {
    use aspis_core::field::M31;
    let words: [u32; 1024] = kani::any();
    let rows: [M31; 1024] = core::array::from_fn(|i| M31(words[i]));
    let j: usize = kani::any();
    kani::assume(j < 1024);
    let coefficients = shipped::Variant::S2.coefficients(&rows);
    assert_eq!(coefficients[j], rows[aspis_r1_builder_reference::row_arithmetic(j)]);
}

// Fixed cells split the actual QM31 wrapper after the full symbolic-index
// timeout. Each retains all4096 arbitrary raw words; these are local gates,
// not a universal wrapper theorem.
#[cfg(kani)]
fn qm31_fixed_cell<const J: usize>() {
    use aspis_core::field::{CM31,M31,QM31};
    let words: [[u32;4];1024] = kani::any();
    let rows: [QM31;1024] = core::array::from_fn(|i| QM31 {
        c0: CM31{a:M31(words[i][0]),b:M31(words[i][1])},
        c1: CM31{a:M31(words[i][2]),b:M31(words[i][3])},
    });
    let coefficients = shipped::Variant::S2.coefficients(&rows);
    assert_eq!(coefficients[J],rows[aspis_r1_builder_reference::row_arithmetic(J)]);
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_0() { qm31_fixed_cell::<0>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_1() { qm31_fixed_cell::<1>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_2() { qm31_fixed_cell::<2>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_3() { qm31_fixed_cell::<3>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_4() { qm31_fixed_cell::<4>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_15() { qm31_fixed_cell::<15>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_16() { qm31_fixed_cell::<16>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_63() { qm31_fixed_cell::<63>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_64() { qm31_fixed_cell::<64>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_255() { qm31_fixed_cell::<255>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_256() { qm31_fixed_cell::<256>(); }

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(1025)]
fn s2_qm31_cell_1023() { qm31_fixed_cell::<1023>(); }
