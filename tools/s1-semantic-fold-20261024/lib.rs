use aspis_core::field::QM31;
mod native {
use super::QM31;
pub(super) fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {
        let boundary = polynomial.iter().copied().fold(polynomial[0], QM31::add);
    boundary
}

pub(super) fn semantic_value(polynomial: &[QM31; 28], alpha: &[QM31; 10], round: usize) -> QM31 {
        let value = polynomial
            .iter()
            .rev()
            .fold(QM31::ZERO, |a, &c| a.mul(alpha[round]).add(c));
    value
}
}
mod reference {
use super::QM31;
pub(super) fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {
    let mut boundary = polynomial[0];
    let mut index = 0usize;
    while index < 28 {
        boundary = QM31::add(boundary, polynomial[index]);
        index += 1;
    }
    boundary
}

pub(super) fn semantic_value(polynomial: &[QM31; 28], alpha: &[QM31; 10], round: usize) -> QM31 {
    let mut index = 28usize;
    let mut value: QM31 = QM31::ZERO;
    while index > 0 {
        index -= 1;
        value = QM31::add(
            QM31::mul(value, alpha[round]),
            polynomial[index],
        );
    }
    value
}
}
#[cfg(kani)] mod proofs;
