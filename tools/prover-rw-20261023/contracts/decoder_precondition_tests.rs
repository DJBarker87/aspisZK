//! Concrete witness retained for the rejected short-QM31 decoder contract.
#[test]
fn short_qm31_is_outside_decoder_contract() {
    let short=[0u8;15];
    assert!(std::panic::catch_unwind(||aspis_core::field::QM31::from_le_bytes(&short)).is_err());
    assert_eq!(aspis_core::field::WideExact::from_le_bytes(&[0u8;31]),None);
}
