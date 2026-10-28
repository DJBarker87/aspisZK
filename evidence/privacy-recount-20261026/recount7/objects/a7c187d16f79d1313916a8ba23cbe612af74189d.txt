//! Drop-free prover-local sparse multilinear evaluation. The field operation
//! order, literal Boolean suffix test and wrong-length rejection are retained.
use aspis_core::field::QM31;
#[derive(Clone, Copy)]
pub struct SparseWeights {
    pub data: [(usize, QM31); 1024],
    pub len: usize,
}
pub fn sparse_eq_weights(point: &[QM31; 10]) -> SparseWeights {
    let mut prefix_len = 10usize;
    while prefix_len > 0
        && (point[prefix_len - 1] == QM31::ZERO || point[prefix_len - 1] == QM31::ONE)
    {
        prefix_len -= 1;
    }
    let trailing_boolean = 10 - prefix_len;
    let mut suffix = 0usize;
    let mut coordinate = prefix_len;
    while coordinate < 10 {
        suffix = (suffix << 1u32) | usize::from(point[coordinate] == QM31::ONE);
        coordinate += 1;
    }
    let mut output = SparseWeights {
        data: [(0, QM31::ZERO); 1024],
        len: 1usize << prefix_len,
    };
    let mut prefix = 0usize;
    while prefix < output.len {
        let row = (prefix << trailing_boolean) | suffix;
        let mut weight = QM31::ONE;
        let mut coordinate = 0usize;
        while coordinate < prefix_len {
            let bit = (prefix >> (prefix_len - 1 - coordinate)) & 1;
            weight = weight.mul(if bit == 0 {
                QM31::ONE.sub(point[coordinate])
            } else {
                point[coordinate]
            });
            coordinate += 1;
        }
        output.data[prefix] = (row, weight);
        prefix += 1;
    }
    output
}
pub fn multilinear_evaluate_qm31(column: &[QM31], point: &[QM31; 10]) -> Option<QM31> {
    if column.len() != 1024 {
        return None;
    }
    let weights = sparse_eq_weights(point);
    let mut sum = QM31::ZERO;
    let mut i = 0usize;
    while i < weights.len {
        let (row, weight) = sparse_weight_at(&weights, i);
        sum = sum.add(weight.mul(column[row]));
        i += 1;
    }
    Some(sum)
}

#[inline(never)]
fn sparse_weight_at(weights: &SparseWeights, i: usize) -> (usize, QM31) { weights.data[i] }
