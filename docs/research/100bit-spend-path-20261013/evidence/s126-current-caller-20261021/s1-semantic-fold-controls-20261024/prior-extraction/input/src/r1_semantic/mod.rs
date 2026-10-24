use crate::aspis_core::field::QM31;

// Extraction-friendly candidate for current production semantic_boundary.
// It preserves the production seed and ascending left-fold order.
fn semantic_boundary(polynomial: &[QM31; 28]) -> QM31 {
    let mut boundary = polynomial[0];
    let mut index = 0usize;
    while index < 28 {
        boundary = QM31::add(boundary, polynomial[index]);
        index += 1;
    }
    boundary
}

// Extraction-friendly candidate for current production semantic_value.
// It preserves the production reverse Horner order and exact add/mul order.
fn semantic_value(polynomial: &[QM31; 28], alpha: &[QM31; 10], round: usize) -> QM31 {
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

pub fn semantic_boundary_entry(polynomial: &[QM31; 28]) -> QM31 {
    semantic_boundary(polynomial)
}

pub fn semantic_value_entry(polynomial: &[QM31; 28], alpha: &[QM31; 10], round: usize) -> QM31 {
    semantic_value(polynomial, alpha, round)
}
