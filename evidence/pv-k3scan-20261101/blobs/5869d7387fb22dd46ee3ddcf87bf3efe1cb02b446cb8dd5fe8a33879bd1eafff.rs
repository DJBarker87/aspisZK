//! Gated terminal arithmetic helpers; same field operation and accumulation order.
use aspis_core::field::{M31, CM31, QM31, P};
#[inline(always)]
fn cm31_mul_r(value: CM31) -> CM31 {
    CM31::new(value.a.double().sub(value.b), value.a.add(value.b.double()))
}
#[derive(Clone, Copy)]
pub(crate) struct PreparedQm31Multiplier {
    components: [[M31; 3]; 3],
}
#[inline(always)]
fn prepare_component(component: CM31) -> [M31; 3] {
    [component.a, component.b, component.a.add(component.b)]
}
#[inline(always)]
fn prepared_component_mul(left: [M31; 3], right: CM31) -> CM31 {
    let m0 = left[0].mul(right.a);
    let m1 = left[1].mul(right.b);
    let m2 = left[2].mul(right.a.add(right.b));
    CM31 {
        a: m0.sub(m1),
        b: m2.sub(m0).sub(m1),
    }
}
impl PreparedQm31Multiplier {
    #[inline(always)]
    pub(crate) fn new(value: QM31) -> Self {
        Self {
            components: [
                prepare_component(value.c0),
                prepare_component(value.c1),
                prepare_component(value.c0.add(value.c1)),
            ],
        }
    }
    #[inline(always)]
    pub(crate) fn mul(self, rhs: QM31) -> QM31 {
        let m0 = prepared_component_mul(self.components[0], rhs.c0);
        let m1 = prepared_component_mul(self.components[1], rhs.c1);
        let m2 = prepared_component_mul(self.components[2], rhs.c0.add(rhs.c1));
        QM31 {
            c0: m0.add(cm31_mul_r(m1)),
            c1: m2.sub(m0).sub(m1),
        }
    }
}
#[inline(always)]
fn reconstruct_component(channels: [u64; 3]) -> CM31 {
    let m0 = M31::reduce_u64(channels[0]);
    let m1 = M31::reduce_u64(channels[1]);
    let m2 = M31::reduce_u64(channels[2]);
    CM31 {
        a: m0.sub(m1),
        b: m2.sub(m0).sub(m1),
    }
}
#[inline(always)]
fn reconstruct_channels(sums: [[u64; 3]; 3]) -> QM31 {
    let m0 = reconstruct_component(sums[0]);
    let m1 = reconstruct_component(sums[1]);
    let m2 = reconstruct_component(sums[2]);
    QM31 {
        c0: m0.add(cm31_mul_r(m1)),
        c1: m2.sub(m0).sub(m1),
    }
}
#[inline(always)]
fn accumulate_channels(mut sums: [[u64; 3]; 3], left: QM31, right: QM31) -> [[u64; 3]; 3] {
    let left_sum = left.c0.add(left.c1);
    let right_sum = right.c0.add(right.c1);
    let a = [
        [left.c0.a, left.c0.b, left.c0.a.add(left.c0.b)],
        [left.c1.a, left.c1.b, left.c1.a.add(left.c1.b)],
        [left_sum.a, left_sum.b, left_sum.a.add(left_sum.b)],
    ];
    let b = [
        [right.c0.a, right.c0.b, right.c0.a.add(right.c0.b)],
        [right.c1.a, right.c1.b, right.c1.a.add(right.c1.b)],
        [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)],
    ];
    sums[0][0] += a[0][0].0 as u64 * b[0][0].0 as u64;
    sums[0][1] += a[0][1].0 as u64 * b[0][1].0 as u64;
    sums[0][2] += a[0][2].0 as u64 * b[0][2].0 as u64;
    sums[1][0] += a[1][0].0 as u64 * b[1][0].0 as u64;
    sums[1][1] += a[1][1].0 as u64 * b[1][1].0 as u64;
    sums[1][2] += a[1][2].0 as u64 * b[1][2].0 as u64;
    sums[2][0] += a[2][0].0 as u64 * b[2][0].0 as u64;
    sums[2][1] += a[2][1].0 as u64 * b[2][1].0 as u64;
    sums[2][2] += a[2][2].0 as u64 * b[2][2].0 as u64;
    sums
}

#[inline(always)]
pub(crate) fn qm31_sum_products2(left: [QM31; 2], right: [QM31; 2]) -> QM31 {
    let sums = [[0u64; 3]; 3];
    let sums = accumulate_channels(sums, left[0], right[0]);
    let sums = accumulate_channels(sums, left[1], right[1]);
    reconstruct_channels(sums)
}

#[inline(always)]
pub(crate) fn qm31_sum_products3(left: [QM31; 3], right: [QM31; 3]) -> QM31 {
    let sums = [[0u64; 3]; 3];
    let sums = accumulate_channels(sums, left[0], right[0]);
    let sums = accumulate_channels(sums, left[1], right[1]);
    let sums = accumulate_channels(sums, left[2], right[2]);
    reconstruct_channels(sums)
}

#[inline(always)]
pub(crate) fn qm31_sum_products4(left: [QM31; 4], right: [QM31; 4]) -> QM31 {
    let sums = [[0u64; 3]; 3];
    let sums = accumulate_channels(sums, left[0], right[0]);
    let sums = accumulate_channels(sums, left[1], right[1]);
    let sums = accumulate_channels(sums, left[2], right[2]);
    let sums = accumulate_channels(sums, left[3], right[3]);
    reconstruct_channels(sums)
}

#[inline(always)]
fn terminal_limb(value: M31) -> u64 { u64::from(value.0) }

#[inline(always)]
pub(crate) fn qm31_pack_base4(values: &[QM31]) -> QM31 {
    assert!(values.len() <= 4);
    let mut padded = [QM31::ZERO; 4];
    let mut i = 0usize;
    while i < values.len() { padded[i] = values[i]; i += 1; }
    let [v0, v1, v2, v3] = padded;
    let p = u64::from(P);


    // Multiplication by u sends (c0,c1) to ((2+i)c1,c0), while
    // multiplication by i sends (a,b) to (-b,a).
    let c0_a = terminal_limb(v0.c0.a)
        + (p - terminal_limb(v1.c0.b))
        + 2 * terminal_limb(v2.c1.a)
        + (p - terminal_limb(v2.c1.b))
        + (p - terminal_limb(v3.c1.a))
        + (2 * p - 2 * terminal_limb(v3.c1.b));
    let c0_b = terminal_limb(v0.c0.b)
        + terminal_limb(v1.c0.a)
        + terminal_limb(v2.c1.a)
        + 2 * terminal_limb(v2.c1.b)
        + 2 * terminal_limb(v3.c1.a)
        + (p - terminal_limb(v3.c1.b));
    let c1_a = terminal_limb(v0.c1.a) + (p - terminal_limb(v1.c1.b)) + terminal_limb(v2.c0.a) + (p - terminal_limb(v3.c0.b));
    let c1_b = terminal_limb(v0.c1.b) + terminal_limb(v1.c1.a) + terminal_limb(v2.c0.b) + terminal_limb(v3.c0.a);

    QM31 {
        c0: CM31::new(M31::reduce_u64(c0_a), M31::reduce_u64(c0_b)),
        c1: CM31::new(M31::reduce_u64(c1_a), M31::reduce_u64(c1_b)),
    }
}

fn accumulate_prepared227(mut sums:[[u64;3];3],right:QM31,left:PreparedQm31Multiplier)->[[u64;3];3] {
    let right_sum=right.c0.add(right.c1);
    let right_components=[
        [right.c0.a,right.c0.b,right.c0.a.add(right.c0.b)],
        [right.c1.a,right.c1.b,right.c1.a.add(right.c1.b)],
        [right_sum.a,right_sum.b,right_sum.a.add(right_sum.b)]];
    sums[0][0]+=left.components[0][0].0 as u64 * right_components[0][0].0 as u64;
    sums[0][1]+=left.components[0][1].0 as u64 * right_components[0][1].0 as u64;
    sums[0][2]+=left.components[0][2].0 as u64 * right_components[0][2].0 as u64;
    sums[1][0]+=left.components[1][0].0 as u64 * right_components[1][0].0 as u64;
    sums[1][1]+=left.components[1][1].0 as u64 * right_components[1][1].0 as u64;
    sums[1][2]+=left.components[1][2].0 as u64 * right_components[1][2].0 as u64;
    sums[2][0]+=left.components[2][0].0 as u64 * right_components[2][0].0 as u64;
    sums[2][1]+=left.components[2][1].0 as u64 * right_components[2][1].0 as u64;
    sums[2][2]+=left.components[2][2].0 as u64 * right_components[2][2].0 as u64;
    sums
}
pub(crate) fn qm31_sum_products3_prepared(left:&[PreparedQm31Multiplier;3],right:&[QM31;3])->QM31 {
    let mut sums=[[0u64;3];3];
    sums=accumulate_prepared227(sums,right[0],left[0]);
    sums=accumulate_prepared227(sums,right[1],left[1]);
    sums=accumulate_prepared227(sums,right[2],left[2]);
    let m0=reconstruct_component(sums[0]);
    let m1=reconstruct_component(sums[1]);
    let m2=reconstruct_component(sums[2]);
    QM31{c0:m0.add(cm31_mul_r(m1)),c1:m2.sub(m0).sub(m1)}
}
pub(crate) fn qm31_m31_dot(weights:&[QM31;7],values:&[M31;7])->QM31 {
    let mut sums=[0u64;4];
    { let mut raw=[0u64;4];
    { let value=values[0].0 as u64; let weight=weights[0];
    raw[0]+=weight.c0.a.0 as u64 *value;
    raw[1]+=weight.c0.b.0 as u64 *value;
    raw[2]+=weight.c1.a.0 as u64 *value;
    raw[3]+=weight.c1.b.0 as u64 *value;
    }
    { let value=values[1].0 as u64; let weight=weights[1];
    raw[0]+=weight.c0.a.0 as u64 *value;
    raw[1]+=weight.c0.b.0 as u64 *value;
    raw[2]+=weight.c1.a.0 as u64 *value;
    raw[3]+=weight.c1.b.0 as u64 *value;
    }
    { let value=values[2].0 as u64; let weight=weights[2];
    raw[0]+=weight.c0.a.0 as u64 *value;
    raw[1]+=weight.c0.b.0 as u64 *value;
    raw[2]+=weight.c1.a.0 as u64 *value;
    raw[3]+=weight.c1.b.0 as u64 *value;
    }
    { let value=values[3].0 as u64; let weight=weights[3];
    raw[0]+=weight.c0.a.0 as u64 *value;
    raw[1]+=weight.c0.b.0 as u64 *value;
    raw[2]+=weight.c1.a.0 as u64 *value;
    raw[3]+=weight.c1.b.0 as u64 *value;
    }
    sums[0]+=M31::reduce_u64(raw[0]).0 as u64;
    sums[1]+=M31::reduce_u64(raw[1]).0 as u64;
    sums[2]+=M31::reduce_u64(raw[2]).0 as u64;
    sums[3]+=M31::reduce_u64(raw[3]).0 as u64;
    }
    { let mut raw=[0u64;4];
    { let value=values[4].0 as u64; let weight=weights[4];
    raw[0]+=weight.c0.a.0 as u64 *value;
    raw[1]+=weight.c0.b.0 as u64 *value;
    raw[2]+=weight.c1.a.0 as u64 *value;
    raw[3]+=weight.c1.b.0 as u64 *value;
    }
    { let value=values[5].0 as u64; let weight=weights[5];
    raw[0]+=weight.c0.a.0 as u64 *value;
    raw[1]+=weight.c0.b.0 as u64 *value;
    raw[2]+=weight.c1.a.0 as u64 *value;
    raw[3]+=weight.c1.b.0 as u64 *value;
    }
    { let value=values[6].0 as u64; let weight=weights[6];
    raw[0]+=weight.c0.a.0 as u64 *value;
    raw[1]+=weight.c0.b.0 as u64 *value;
    raw[2]+=weight.c1.a.0 as u64 *value;
    raw[3]+=weight.c1.b.0 as u64 *value;
    }
    sums[0]+=M31::reduce_u64(raw[0]).0 as u64;
    sums[1]+=M31::reduce_u64(raw[1]).0 as u64;
    sums[2]+=M31::reduce_u64(raw[2]).0 as u64;
    sums[3]+=M31::reduce_u64(raw[3]).0 as u64;
    }
    QM31{c0:CM31::new(M31::reduce_u64(sums[0]),M31::reduce_u64(sums[1])),c1:CM31::new(M31::reduce_u64(sums[2]),M31::reduce_u64(sums[3]))}
}

pub fn source_trace13(left:&[PreparedQm31Multiplier;3],right:&[QM31;3])->Vec<[[u64;3];3]> {
 let mut trace=Vec::new();

    let mut sums = [[0u64; 3]; 3];
    for index in 0..3 {
        let right_sum = right[index].c0.add(right[index].c1);
        let right_components = [
            [
                right[index].c0.a,
                right[index].c0.b,
                right[index].c0.a.add(right[index].c0.b),
            ],
            [
                right[index].c1.a,
                right[index].c1.b,
                right[index].c1.a.add(right[index].c1.b),
            ],
            [right_sum.a, right_sum.b, right_sum.a.add(right_sum.b)],
        ];
        for component in 0..3 {
            for channel in 0..3 {
                sums[component][channel] += left[index].components[component][channel].0 as u64
                    * right_components[component][channel].0 as u64;
                trace.push(sums);
            }
        }
    }
    
trace
}

fn traced_accumulate13(mut sums:[[u64;3];3],right:QM31,left:PreparedQm31Multiplier,trace:&mut Vec<[[u64;3];3]>)->[[u64;3];3] {
    let right_sum=right.c0.add(right.c1);
    let right_components=[
        [right.c0.a,right.c0.b,right.c0.a.add(right.c0.b)],
        [right.c1.a,right.c1.b,right.c1.a.add(right.c1.b)],
        [right_sum.a,right_sum.b,right_sum.a.add(right_sum.b)]];
    sums[0][0]+=left.components[0][0].0 as u64 * right_components[0][0].0 as u64; trace.push(sums);
    sums[0][1]+=left.components[0][1].0 as u64 * right_components[0][1].0 as u64; trace.push(sums);
    sums[0][2]+=left.components[0][2].0 as u64 * right_components[0][2].0 as u64; trace.push(sums);
    sums[1][0]+=left.components[1][0].0 as u64 * right_components[1][0].0 as u64; trace.push(sums);
    sums[1][1]+=left.components[1][1].0 as u64 * right_components[1][1].0 as u64; trace.push(sums);
    sums[1][2]+=left.components[1][2].0 as u64 * right_components[1][2].0 as u64; trace.push(sums);
    sums[2][0]+=left.components[2][0].0 as u64 * right_components[2][0].0 as u64; trace.push(sums);
    sums[2][1]+=left.components[2][1].0 as u64 * right_components[2][1].0 as u64; trace.push(sums);
    sums[2][2]+=left.components[2][2].0 as u64 * right_components[2][2].0 as u64; trace.push(sums);
    sums
}
pub fn owned_trace13(left:&[PreparedQm31Multiplier;3],right:&[QM31;3])->Vec<[[u64;3];3]> {
 let mut sums=[[0u64;3];3];let mut trace=Vec::new();
 sums=traced_accumulate13(sums,right[0],left[0],&mut trace);
 sums=traced_accumulate13(sums,right[1],left[1],&mut trace);
 let _=traced_accumulate13(sums,right[2],left[2],&mut trace);trace
}
