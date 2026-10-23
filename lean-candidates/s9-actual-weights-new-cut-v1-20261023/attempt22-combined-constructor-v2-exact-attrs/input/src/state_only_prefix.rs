use crate::field::QM31;

fn state_only_statement_points(z: &[QM31; 10]) -> [[QM31; 10]; 3] {
    let mut successor = *z;
    let mut carry = QM31::ONE;
    for coordinate in (0..z.len()).rev() {
        let bit = z[coordinate];
        let bit_and_carry = bit.mul(carry);
        successor[coordinate] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
        carry = bit_and_carry;
    }
    let mut absorption = *z;
    absorption[7] = QM31::ONE.sub(absorption[7]);
    absorption[6] = QM31::ONE.sub(absorption[6]);
    [*z, successor, absorption]
}

pub mod r0 {
    use super::QM31;

    /// MSB-first semantic coordinates; reverse these for R-D's eqWeight.
    pub fn statement_points(alpha: &[QM31; 10]) -> [[QM31; 10]; 3] {
        super::state_only_statement_points(alpha)
    }
}
