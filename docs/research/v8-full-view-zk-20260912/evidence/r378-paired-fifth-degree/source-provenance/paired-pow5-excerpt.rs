// Source lines 123-127 (inclusive) from the frozen file below.
#[inline(always)]
fn pow5(value: QM31) -> QM31 {
    let square = value.square();
    square.square().mul(value)
}

// Source lines 343-357 (inclusive) from the frozen file below.
/// Full round whose constants are pinned base-field values. Only c0.a changes
/// during the addition, avoiding three zero-limb additions per lane in the
/// two fixed leading rounds.
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

// Source lines 388-399 (inclusive) from the frozen file below.

fn leading_pair(openings: &StateOnlyPoseidonOpenings) -> [QM31; POSEIDON2_WIDTH] {
    let mut state = openings.z;
    for lane in 0..RATE {
        state[lane] = state[lane].add(openings.xor12_z[lane]);
    }
    external_linear_lazy(&mut state);
    full_round_m31_constants(
        full_round_m31_constants(state, EXTERNAL_INITIAL[0]),
        EXTERNAL_INITIAL[1],
    )
}

// Source lines 484-502 (inclusive) from the frozen file below.
fn interpolated_full_pair(
    state: [QM31; POSEIDON2_WIDTH],
    local: &[QM31; 16],
) -> [QM31; POSEIDON2_WIDTH] {
    let weights = [local[1], local[9], local[10]];
    let even = interpolate_three_constant_columns(
        weights,
        EXTERNAL_INITIAL[2],
        EXTERNAL_FINAL[0],
        EXTERNAL_FINAL[2],
    );
    let odd = interpolate_three_constant_columns(
        weights,
        EXTERNAL_INITIAL[3],
        EXTERNAL_FINAL[1],
        EXTERNAL_FINAL[3],
    );
    full_round(full_round(state, even), odd)
}

