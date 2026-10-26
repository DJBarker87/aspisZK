//! Owned safe loop-free reference; parent is cfg(kani)-only.
use aspis_core::field::{QM31,CM31,M31,PreparedQm31Multiplier};
fn mul_by_r(x: CM31) -> CM31 {
    // (2 + i)(a + bi) = (2a - b) + (a + 2b) i
    CM31 {
        a: x.a.double().sub(x.b),
        b: x.a.add(x.b.double()),
    }
}
fn qm31_from_karatsuba_channel_sums(sums: [[u64; 3]; 3]) -> QM31 {
    let reconstruct = |channels: [u64; 3]| {
        let m0 = M31::reduce_u64(channels[0]);
        let m1 = M31::reduce_u64(channels[1]);
        let m2 = M31::reduce_u64(channels[2]);
        CM31 {
            a: m0.sub(m1),
            b: m2.sub(m0).sub(m1),
        }
    };
    let m0 = reconstruct(sums[0]);
    let m1 = reconstruct(sums[1]);
    let m2 = reconstruct(sums[2]);
    QM31 {
        c0: m0.add(mul_by_r(m1)),
        c1: m2.sub(m0).sub(m1),
    }
}
fn qm31_accumulate_product_channels(
    mut sums: [[u64; 3]; 3],
    left: QM31,
    right: QM31,
) -> [[u64; 3]; 3] {
    let left_sum = left.c0.add(left.c1);
    let right_sum = right.c0.add(right.c1);
    let left_components = [
        [left.c0.a, left.c0.b, left.c0.a.add(left.c0.b)],
        [left.c1.a, left.c1.b, left.c1.a.add(left.c1.b)],
        [left_sum.a, left_sum.b, left_sum.a.add(left_sum.b)],
    ];
    let right_components = [
        [right.c0.a, right.c0.b, right.c0.a.add(right.c0.b)],
        [right.c1.a, right.c1.b, right.c1.a.add(right.c1.b)],
        [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)],
    ];
    sums[0][0] += left_components[0][0].0 as u64 * right_components[0][0].0 as u64;
    sums[0][1] += left_components[0][1].0 as u64 * right_components[0][1].0 as u64;
    sums[0][2] += left_components[0][2].0 as u64 * right_components[0][2].0 as u64;
    sums[1][0] += left_components[1][0].0 as u64 * right_components[1][0].0 as u64;
    sums[1][1] += left_components[1][1].0 as u64 * right_components[1][1].0 as u64;
    sums[1][2] += left_components[1][2].0 as u64 * right_components[1][2].0 as u64;
    sums[2][0] += left_components[2][0].0 as u64 * right_components[2][0].0 as u64;
    sums[2][1] += left_components[2][1].0 as u64 * right_components[2][1].0 as u64;
    sums[2][2] += left_components[2][2].0 as u64 * right_components[2][2].0 as u64;
    sums
}
fn sum_products3(left:[QM31;3],right:[QM31;3])->QM31 {
 let s=qm31_accumulate_product_channels([[0u64;3];3],left[0],right[0]);
 let s=qm31_accumulate_product_channels(s,left[1],right[1]);
 let s=qm31_accumulate_product_channels(s,left[2],right[2]);
 qm31_from_karatsuba_channel_sums(s)
}
fn block_value(polynomial:&[QM31;28],powers:[QM31;3],block:usize)->QM31 {
 let start=4*block;
 polynomial[start].add(sum_products3(powers,[polynomial[start+1],polynomial[start+2],polynomial[start+3]]))
}
pub fn evaluate(polynomial:&[QM31;28],challenge:QM31)->QM31 {
 let x2=challenge.square();let x3=challenge.mul(x2);let x4=x2.square();
 let powers=[challenge,x2,x3];let prepared_x4=PreparedQm31Multiplier::new(x4);
 let accumulator=block_value(polynomial,powers,6);
 let accumulator=prepared_x4.mul(accumulator).add(block_value(polynomial,powers,5));
 let accumulator=prepared_x4.mul(accumulator).add(block_value(polynomial,powers,4));
 let accumulator=prepared_x4.mul(accumulator).add(block_value(polynomial,powers,3));
 let accumulator=prepared_x4.mul(accumulator).add(block_value(polynomial,powers,2));
 let accumulator=prepared_x4.mul(accumulator).add(block_value(polynomial,powers,1));
 let accumulator=prepared_x4.mul(accumulator).add(block_value(polynomial,powers,0));
 accumulator
}
