use aspis_core::field::QM31;
fn equality_factor(a: QM31, b: QM31) -> QM31 {
    let ab = a.mul(b);
    QM31::ONE.sub(a).sub(b).add(ab).add(ab)
}
pub fn equality_value13(left: [QM31; 10], right: [QM31; 10]) -> QM31 {
    let mut product = equality_factor(left[0], right[0]);
    let mut index = 1usize;
    while index < left.len() {
        product = product.mul(equality_factor(left[index], right[index]));
        index += 1;
    }
    product
}

pub fn source_equality13(left: &[QM31; 10], right: &[QM31; 10]) -> QM31 {
    let mut product = equality_factor(left[0], right[0]);
    let mut index = 1usize;
    while index < left.len() {
        product = product.mul(equality_factor(left[index], right[index]));
        index += 1;
    }
    product
}

pub fn flat_equality13(left: &[QM31;10], right: &[QM31;10]) -> QM31 {
    let mut product=equality_factor(left[0],right[0]);
    product=product.mul(equality_factor(left[1],right[1]));
    product=product.mul(equality_factor(left[2],right[2]));
    product=product.mul(equality_factor(left[3],right[3]));
    product=product.mul(equality_factor(left[4],right[4]));
    product=product.mul(equality_factor(left[5],right[5]));
    product=product.mul(equality_factor(left[6],right[6]));
    product=product.mul(equality_factor(left[7],right[7]));
    product=product.mul(equality_factor(left[8],right[8]));
    product=product.mul(equality_factor(left[9],right[9]));
    product
}

pub fn source_mask13(values: &[QM31; 16], mut mask: u16) -> QM31 {
    let complement = mask.count_ones() > 8;
    if complement {
        mask = !mask;
    }
    let mut sum = if complement { QM31::ONE } else { QM31::ZERO };
    while mask != 0 {
        let index = mask.trailing_zeros() as usize;
        sum = if complement {
            sum.sub(values[index])
        } else {
            sum.add(values[index])
        };
        mask &= mask - 1;
    }
    sum
}

pub fn owned_mask13(values:[QM31;16],mask:u16)->QM31 {
    match mask {
        1749 => QM31::ZERO.add(values[0]).add(values[2]).add(values[4]).add(values[6]).add(values[7]).add(values[9]).add(values[10]),
        2048 => QM31::ZERO.add(values[11]),
        2049 => QM31::ZERO.add(values[0]).add(values[11]),
        4097 => QM31::ZERO.add(values[0]).add(values[12]),
        6144 => QM31::ZERO.add(values[11]).add(values[12]),
        6145 => QM31::ZERO.add(values[0]).add(values[11]).add(values[12]),
        26214 => QM31::ZERO.add(values[1]).add(values[2]).add(values[5]).add(values[6]).add(values[9]).add(values[10]).add(values[13]).add(values[14]),
        _ => panic!("outside frozen active mask set"),
    }
}
