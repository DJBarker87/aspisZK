//! P6 fallback preparation only. Parent crate is cfg(kani)-only.
//! No proof or source association is claimed before the native and Lean gates.
use aspis_core::field::QM31;

// The decreasing counter starts at ten. Each recursive call reads and writes
// exactly one coordinate; the caller supplies no bound or desired output.
fn successor(
    point: &[QM31; 10],
    remaining: usize,
    carry: QM31,
    mut output: [QM31; 10],
) -> [QM31; 10] {
    if remaining == 0 {
        output
    } else {
        let coordinate = remaining - 1;
        let bit = point[coordinate];
        let product = bit.mul(carry);
        output[coordinate] = bit.add(carry).sub(product.add(product));
        successor(point, coordinate, product, output)
    }
}

pub fn statement_points(point: &[QM31; 10]) -> [[QM31; 10]; 3] {
    let next = successor(point, 10, QM31::ONE, *point);
    let mut absorption = *point;
    absorption[7] = QM31::ONE.sub(absorption[7]);
    absorption[6] = QM31::ONE.sub(absorption[6]);
    [*point, next, absorption]
}
