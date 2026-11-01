use aspis_core::field::QM31;
pub fn evaluate(polynomial: &[QM31;28], challenge: QM31) -> QM31 {
    aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(polynomial, challenge)
}
