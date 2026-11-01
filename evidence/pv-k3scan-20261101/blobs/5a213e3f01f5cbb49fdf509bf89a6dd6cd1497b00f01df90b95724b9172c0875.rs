use alloc::vec::Vec;
use aspis_core::field::QM31;
use aspis_statement::trace_v4::TRACE_ROWS;
fn eq_row(point: &[QM31; 10], row: usize) -> QM31 {
    let mut weight = QM31::ONE;
    for (coordinate, value) in point.iter().enumerate() {
        let bit = (row >> (point.len() - 1 - coordinate)) & 1;
        weight = weight.mul(if bit == 0 {
            QM31::ONE.sub(*value)
        } else {
            *value
        });
    }
    weight
}
fn sparse_eq_weights(point: &[QM31; 10]) -> Vec<(usize, QM31)> {
    let trailing_boolean = point
        .iter()
        .rev()
        .take_while(|value| **value == QM31::ZERO || **value == QM31::ONE)
        .count();
    let prefix_len = point.len() - trailing_boolean;
    let mut suffix = 0usize;
    for coordinate in &point[prefix_len..] {
        suffix = (suffix << 1) | usize::from(*coordinate == QM31::ONE);
    }
    let mut weights = Vec::with_capacity(1usize << prefix_len);
    for prefix in 0..(1usize << prefix_len) {
        let row = (prefix << trailing_boolean) | suffix;
        let mut weight = QM31::ONE;
        for (coordinate, value) in point[..prefix_len].iter().enumerate() {
            let bit = (prefix >> (prefix_len - 1 - coordinate)) & 1;
            weight = weight.mul(if bit == 0 {
                QM31::ONE.sub(*value)
            } else {
                *value
            });
        }
        weights.push((row, weight));
    }
    weights
}
pub fn multilinear_evaluate_qm31(column: &[QM31], point: &[QM31; 10]) -> Option<QM31> {
    if column.len() != TRACE_ROWS {
        return None;
    }
    Some(
        sparse_eq_weights(point)
            .into_iter()
            .fold(QM31::ZERO, |sum, (row, weight)| {
                sum.add(weight.mul(column[row]))
            }),
    )
}
