/// Extraction-only by-value wrapper. Body is one call to the shipped function.
/// The cfg-gated shim changes no shipped compressor code.
#[cfg(aeneas_ref)]
pub fn compress16_by_value(
    tag: aspis_core::field::M31,
    values: [aspis_core::field::M31; 16],
    lambda: aspis_core::field::QM31,
) -> aspis_core::field::QM31 {
    aspis_statement::logup::compress_tagged_tuple(tag, &values, lambda)
}
