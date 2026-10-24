fn semantic_value(polynomial: &[QM31; 28], alpha: &[QM31; 10], round: usize) -> QM31 {
        let value = polynomial
            .iter()
            .rev()
            .fold(QM31::ZERO, |a, &c| a.mul(alpha[round]).add(c));
    value
}
