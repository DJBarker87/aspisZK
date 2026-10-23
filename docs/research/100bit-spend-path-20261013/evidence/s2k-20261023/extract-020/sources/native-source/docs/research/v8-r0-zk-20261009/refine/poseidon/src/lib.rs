//! Extraction-friendly copy of the Poseidon2-M31 permutation as the builder
//! uses it (permute_optimized_with_trace, crates/aspis-statement/src/poseidon2.rs:362-410,
//! read-only from origin/codex/100bit-spend-path-20261013), producing the eleven
//! odd-round outputs (DESIGN-BUILDER-MODEL §11).  One round per function; the
//! round functions take their constants as ARGUMENTS; only perm_rounds reads
//! the tables (copied literally from poseidon2.rs:83-134).  Field arithmetic is
//! canonical M31 with one u64 reduction per operation (no lazy multi-step folds).
#![no_std]

pub const P: u32 = 0x7fff_ffff;

pub const EXTERNAL_INITIAL: [[u32; 16]; 4] = [
    [
        0x768bab52, 0x70e0ab7d, 0x3d266c8a, 0x6da42045, 0x600fef22, 0x41dace6b, 0x64f9bdd4,
        0x5d42d4fe, 0x76b1516d, 0x6fc9a717, 0x70ac4fb6, 0x00194ef6, 0x22b644e2, 0x1f7916d5,
        0x47581be2, 0x2710a123,
    ],
    [
        0x6284e867, 0x018d3afe, 0x5df99ef3, 0x4c1e467b, 0x566f6abc, 0x2994e427, 0x538a6d42,
        0x5d7bf2cf, 0x7fda2dab, 0x0fd854c4, 0x46922fca, 0x3d7763a1, 0x19fd05ca, 0x0a4bbb43,
        0x15075851, 0x3d903d76,
    ],
    [
        0x2d290ff7, 0x40809fa0, 0x59dac6ec, 0x127927a2, 0x6bbf0ea0, 0x0294140f, 0x24742976,
        0x6e84c081, 0x22484f4a, 0x354cae59, 0x0453ffe1, 0x3f47a3cc, 0x0088204e, 0x6066e109,
        0x3b7c4b80, 0x6b55665d,
    ],
    [
        0x3bc4b897, 0x735bf378, 0x508daf42, 0x1884fc2b, 0x7214f24c, 0x7498be0a, 0x1a60e640,
        0x3303f928, 0x29b46376, 0x5c96bb68, 0x65d097a5, 0x1d358e9f, 0x4a9a9017, 0x4724cf76,
        0x347af70f, 0x1e77e59a,
    ],
];
pub const EXTERNAL_FINAL: [[u32; 16]; 4] = [
    [
        0x57090613, 0x1fa42108, 0x17bbef50, 0x1ff7e11c, 0x047b24ca, 0x4e140275, 0x4fa086f5,
        0x079b309c, 0x1159bd47, 0x6d37e4e5, 0x075d8dce, 0x12121ca0, 0x7f6a7c40, 0x68e182ba,
        0x5493201b, 0x0444a80e,
    ],
    [
        0x0064f4c6, 0x6467abe6, 0x66975762, 0x2af68f9b, 0x345b33be, 0x1b70d47f, 0x053db717,
        0x381189cb, 0x43b915f8, 0x20df3694, 0x0f459d26, 0x77a0e97b, 0x2f73e739, 0x1876c2f9,
        0x65a0e29a, 0x4cabefbe,
    ],
    [
        0x5abd1268, 0x4d34a760, 0x12771799, 0x69a0c9ac, 0x39091e55, 0x7f611cd0, 0x3af055da,
        0x7ac0bbdf, 0x6e0f3a24, 0x41e3b6f7, 0x49b3756d, 0x568bc538, 0x20c079d8, 0x1701c72c,
        0x7670dc6c, 0x5a439035,
    ],
    [
        0x7c93e00e, 0x561fbb4d, 0x1178907b, 0x02737406, 0x32fb24f1, 0x6323b60a, 0x6ab12418,
        0x42c99cea, 0x155a0b97, 0x53d1c6aa, 0x2bd20347, 0x279b3d73, 0x4f5f3c70, 0x0245af6c,
        0x238359d3, 0x49966a59,
    ],
];
pub const INTERNAL: [u32; 14] = [
    0x7f7ec4bf, 0x0421926f, 0x5198e669, 0x34db3148, 0x4368bafd, 0x66685c7f, 0x78d3249a, 0x60187881,
    0x76dad67a, 0x0690b437, 0x1ea95311, 0x40e5369a, 0x38f103fc, 0x1d226a21,
];
pub const INTERNAL_SHIFTS: [u32; 15] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16];

pub fn m31_add(a: u32, b: u32) -> u32 {
    ((a as u64 + b as u64) % (P as u64)) as u32
}

pub fn m31_mul(a: u32, b: u32) -> u32 {
    ((a as u64 * b as u64) % (P as u64)) as u32
}

/// pow5 (poseidon2.rs:136-140): (x^2)^2 * x.
pub fn pow5(x: u32) -> u32 {
    let square = m31_mul(x, x);
    m31_mul(m31_mul(square, square), x)
}

/// apply_mat4 (poseidon2.rs:143-154 / 182-191): one four-lane group.
pub fn mat4(a: u32, b: u32, c: u32, d: u32) -> [u32; 4] {
    let (a, b, c, d) = (a as u64, b as u64, c as u64, d as u64);
    let p = P as u64;
    [
        ((2 * a + 3 * b + c + d) % p) as u32,
        ((a + 2 * b + 3 * c + d) % p) as u32,
        ((a + b + 2 * c + 3 * d) % p) as u32,
        ((3 * a + b + c + 2 * d) % p) as u32,
    ]
}

/// External layer, part 1: mat4 on each group of four lanes.
pub fn ext_groups(state: &[u32; 16]) -> [u32; 16] {
    let mut out = [0u32; 16];
    let mut g: usize = 0;
    while g < 4 {
        let m = mat4(state[4 * g], state[4 * g + 1], state[4 * g + 2], state[4 * g + 3]);
        out[4 * g] = m[0];
        out[4 * g + 1] = m[1];
        out[4 * g + 2] = m[2];
        out[4 * g + 3] = m[3];
        g += 1;
    }
    out
}

/// External layer, part 2: the four column sums.
pub fn ext_sums(grouped: &[u32; 16]) -> [u32; 4] {
    let mut sums = [0u32; 4];
    let mut col: usize = 0;
    while col < 4 {
        let s = grouped[col] as u64 + grouped[4 + col] as u64 + grouped[8 + col] as u64 + grouped[12 + col] as u64;
        sums[col] = (s % (P as u64)) as u32;
        col += 1;
    }
    sums
}

/// External layer, part 3: add the column sum to every lane.
pub fn ext_add(grouped: &[u32; 16], sums: &[u32; 4]) -> [u32; 16] {
    let mut out = [0u32; 16];
    let mut i: usize = 0;
    while i < 16 {
        out[i] = m31_add(grouped[i], sums[i % 4]);
        i += 1;
    }
    out
}

/// external_linear_lazy (poseidon2.rs:194-202).
pub fn external_linear(state: &[u32; 16]) -> [u32; 16] {
    let grouped = ext_groups(state);
    let sums = ext_sums(&grouped);
    ext_add(&grouped, &sums)
}

/// Internal layer, part 1: the sum of lanes 1..15.
pub fn int_part_sum(state: &[u32; 16]) -> u32 {
    let mut acc: u64 = 0;
    let mut i: usize = 1;
    while i < 16 {
        acc += state[i] as u64;
        i += 1;
    }
    (acc % (P as u64)) as u32
}

/// internal_linear_lazy (poseidon2.rs:216-224).
pub fn internal_linear(state: &[u32; 16], shifts: &[u32; 15]) -> [u32; 16] {
    let part = int_part_sum(state);
    let full = m31_add(part, state[0]);
    let mut out = [0u32; 16];
    out[0] = ((part as u64 + P as u64 - state[0] as u64) % (P as u64)) as u32;
    let mut i: usize = 1;
    while i < 16 {
        out[i] = ((full as u64 + ((state[i] as u64) << shifts[i - 1])) % (P as u64)) as u32;
        i += 1;
    }
    out
}

/// The S-box layer of a full round: lane i <- pow5(state[i] + c[i]).
pub fn sbox_full(state: &[u32; 16], c: &[u32; 16]) -> [u32; 16] {
    let mut out = [0u32; 16];
    let mut i: usize = 0;
    while i < 16 {
        out[i] = pow5(m31_add(state[i], c[i]));
        i += 1;
    }
    out
}

/// One full (external) round.
pub fn full_round(state: &[u32; 16], c: &[u32; 16]) -> [u32; 16] {
    external_linear(&sbox_full(state, c))
}

/// One internal round.
pub fn internal_round(state: &[u32; 16], c0: u32, shifts: &[u32; 15]) -> [u32; 16] {
    let mut s = *state;
    s[0] = pow5(m31_add(state[0], c0));
    internal_linear(&s, shifts)
}

/// Absorb lanes 0..7 into the pre-state.
pub fn absorb_into(pre: &[u32; 16], absorb: &[u32; 16]) -> [u32; 16] {
    let mut out = *pre;
    let mut i: usize = 0;
    while i < 8 {
        out[i] = m31_add(pre[i], absorb[i]);
        i += 1;
    }
    out
}

/// Row 0: absorption, the leading external layer, rounds 0 and 1.
pub fn leading_pair(pre: &[u32; 16], absorb: &[u32; 16], c0: &[u32; 16], c1: &[u32; 16]) -> [u32; 16] {
    let s = external_linear(&absorb_into(pre, absorb));
    full_round(&full_round(&s, c0), c1)
}

/// Round `round` (0..22) with the pinned tables.
pub fn apply_round(state: &[u32; 16], round: usize) -> [u32; 16] {
    if round < 4 {
        full_round(state, &EXTERNAL_INITIAL[round])
    } else if round < 18 {
        internal_round(state, INTERNAL[round - 4], &INTERNAL_SHIFTS)
    } else {
        full_round(state, &EXTERNAL_FINAL[round - 18])
    }
}

/// The eleven odd-round outputs for a block with this pre-state and absorption.
pub fn perm_rounds(pre: &[u32; 16], absorb: &[u32; 16]) -> [[u32; 16]; 11] {
    let mut rounds = [[0u32; 16]; 11];
    let mut state = leading_pair(pre, absorb, &EXTERNAL_INITIAL[0], &EXTERNAL_INITIAL[1]);
    rounds[0] = state;
    let mut k: usize = 1;
    while k < 11 {
        state = apply_round(&apply_round(&state, 2 * k), 2 * k + 1);
        rounds[k] = state;
        k += 1;
    }
    rounds
}
