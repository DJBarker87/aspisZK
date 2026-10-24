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
