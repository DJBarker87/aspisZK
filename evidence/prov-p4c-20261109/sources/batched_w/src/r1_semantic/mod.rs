use crate::aspis_core::field::QM31;

fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {
        let boundary = polynomial.iter().copied().fold(polynomial[0], QM31::add);
    boundary
}

fn semantic_value(polynomial: &[QM31; 28], alpha: &[QM31; 10], round: usize) -> QM31 {
        let value: QM31 = polynomial
            .iter()
            .rev()
            .fold(QM31::ZERO, |a, &c| a.mul(alpha[round]).add(c));
    value
}

pub fn semantic_boundary_entry(polynomial: &[QM31; 28]) -> QM31 {
    semantic_boundary(polynomial)
}

pub fn semantic_value_entry(polynomial: &[QM31; 28], alpha: &[QM31; 10], round: usize) -> QM31 {
    semantic_value(polynomial, alpha, round)
}
