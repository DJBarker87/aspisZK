#![cfg(aeneas_ref)]
//! Extraction-only wrapper; the body is one call to the shipped compressor.
//! No production source body or attribute is changed.
pub fn compress16_by_value(
    tag: aspis_core::field::M31,
    values: [aspis_core::field::M31; 16],
    lambda: aspis_core::field::QM31,
) -> aspis_core::field::QM31 {
    aspis_statement::logup::compress_tagged_tuple(tag, &values, lambda)
}
