use aspis_core::field::{M31,CM31,QM31,P};
use aspis_statement::poseidon2::{POSEIDON2_WIDTH,RATE};
#[inline(always)]
fn extension_limbs(value: QM31) -> [u32; 4] {
    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
}
#[inline(always)]
fn extension_from_raw_limbs(limbs: [u64; 4]) -> QM31 {
    QM31 {
        c0: CM31::new(M31::reduce_u62(limbs[0]), M31::reduce_u62(limbs[1])),
        c1: CM31::new(M31::reduce_u62(limbs[2]), M31::reduce_u62(limbs[3])),
    }
}
#[inline(always)]
fn pow5(value: QM31) -> QM31 {
    let square = value.square();
    square.square().mul(value)
}
#[inline(never)]
fn external_linear_lazy(state: &mut [QM31; POSEIDON2_WIDTH]) {
    let mut group = 0usize;
    while group < 4 {
        let start = 4 * group;
        let input = [
            state[start],
            state[start + 1],
            state[start + 2],
            state[start + 3],
        ];
        let input = input.map(extension_limbs);
        let mut output = 0usize;
        while output < 4 {
            let raw = core::array::from_fn(|limb| {
                let a = u64::from(input[0][limb]);
                let b = u64::from(input[1][limb]);
                let c = u64::from(input[2][limb]);
                let d = u64::from(input[3][limb]);
                match output {
                    0 => 2 * a + 3 * b + c + d,
                    1 => a + 2 * b + 3 * c + d,
                    2 => a + b + 2 * c + 3 * d,
                    3 => 3 * a + b + c + 2 * d,
                    _ => unreachable!(),
                }
            });
            state[start + output] = extension_from_raw_limbs(raw);
            output += 1;
        }
        group += 1;
    }
    let sums: [[u64; 4]; 4] = core::array::from_fn(|column| {
        core::array::from_fn(|limb| {
            u64::from(extension_limbs(state[column])[limb])
                + u64::from(extension_limbs(state[4 + column])[limb])
                + u64::from(extension_limbs(state[8 + column])[limb])
                + u64::from(extension_limbs(state[12 + column])[limb])
        })
    });
    let mut index = 0usize;
    while index < POSEIDON2_WIDTH {
        let limbs = extension_limbs(state[index]);
        state[index] = extension_from_raw_limbs(core::array::from_fn(|limb| {
            u64::from(limbs[limb]) + sums[index & 3][limb]
        }));
        index += 1;
    }
}
#[inline(always)]
fn external_local_packed_raw(input: [QM31; 4]) -> [u64; 4] {
    let input = input.map(extension_limbs);
    let local: [[u64; 4]; 4] = core::array::from_fn(|output| {
        core::array::from_fn(|limb| {
            let a = u64::from(input[0][limb]);
            let b = u64::from(input[1][limb]);
            let c = u64::from(input[2][limb]);
            let d = u64::from(input[3][limb]);
            match output {
                0 => 2 * a + 3 * b + c + d,
                1 => a + 2 * b + 3 * c + d,
                2 => a + b + 2 * c + 3 * d,
                3 => 3 * a + b + c + 2 * d,
                _ => unreachable!(),
            }
        })
    });
    let mut all_local_limbs_bounded = true;
    let mut output = 0usize;
    while output < 4 {
        let mut limb = 0usize;
        while limb < 4 {
            all_local_limbs_bounded &= local[output][limb] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            limb += 1;
        }
        output += 1;
    }
    debug_assert!(all_local_limbs_bounded);

    let bound = EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
    let packed = [
        local[0][0] + 5 * bound - local[1][1] + 2 * local[2][2]
            - local[2][3]
            - local[3][2]
            - 2 * local[3][3],
        local[0][1] + local[1][0] + local[2][2] + 2 * local[2][3] + 2 * local[3][2] + bound
            - local[3][3],
        local[0][2] + 2 * bound - local[1][3] + local[2][0] - local[3][1],
        local[0][3] + local[1][2] + local[2][1] + local[3][0],
    ];
    debug_assert!(packed[0] < 8 * bound);
    debug_assert!(packed[1] < 8 * bound);
    debug_assert!(packed[2] < 4 * bound);
    debug_assert!(packed[3] < 4 * bound);
    packed
}
#[inline(always)]
fn external_local_packed(input: [QM31; 4]) -> QM31 {
    extension_from_raw_limbs(external_local_packed_raw(input))
}
#[inline(never)]
fn external_linear_packed(state: [QM31; POSEIDON2_WIDTH]) -> [QM31; 4] {
    let mut local_packed = [QM31::ZERO; 4];
    let mut group = 0usize;
    while group < 4 {
        let start = 4 * group;
        let input = [
            state[start],
            state[start + 1],
            state[start + 2],
            state[start + 3],
        ];
        local_packed[group] = external_local_packed(input);
        group += 1;
    }
    let sum = QM31::ZERO
        .add(local_packed[0])
        .add(local_packed[1])
        .add(local_packed[2])
        .add(local_packed[3]);
    local_packed.map(|value| value.add(sum))
}
#[inline(never)]
fn full_round(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [QM31; POSEIDON2_WIDTH],
) -> [QM31; POSEIDON2_WIDTH] {
    for lane in 0..POSEIDON2_WIDTH {
        state[lane] = pow5(state[lane].add(constants[lane]));
    }
    external_linear_lazy(&mut state);
    state
}
#[inline(never)]
fn full_round_m31_constants(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [u32; POSEIDON2_WIDTH],
) -> [QM31; POSEIDON2_WIDTH] {
    for lane in 0..POSEIDON2_WIDTH {
        state[lane].c0.a = state[lane].c0.a.add(M31(constants[lane]));
        state[lane] = pow5(state[lane]);
    }
    external_linear_lazy(&mut state);
    state
}
#[inline(never)]
fn full_round_packed(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [QM31; POSEIDON2_WIDTH],
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    for lane in 0..POSEIDON2_WIDTH {
        state[lane] = pow5(state[lane].add(constants[lane]));
    }
    external_linear_packed(state)
}
#[inline(never)]
fn full_round_m31_constants_packed(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [u32; POSEIDON2_WIDTH],
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    for lane in 0..POSEIDON2_WIDTH {
        state[lane].c0.a = state[lane].c0.a.add(M31(constants[lane]));
        state[lane] = pow5(state[lane]);
    }
    external_linear_packed(state)
}
pub const STATE_ONLY_POSEIDON_PACKED_LANES: usize = POSEIDON2_WIDTH / 4;
const EXTERNAL_LOCAL_LIMB_MODULUS_BOUND: u64 = 7 * P as u64;
