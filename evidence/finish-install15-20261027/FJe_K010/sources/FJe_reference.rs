// Owned safe references. Compiled only in the isolated cfg(kani) evidence crate.
#[cfg(kani)]
#[allow(non_snake_case)]
mod FJe_reference {
    use super::*;

    fn rows(input: [QM31;4]) -> [[u64;4];4] {
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
        local
    }
    fn local_raw(input: [QM31; 4]) -> [u64; 4] {
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

    fn local(input: [QM31;4]) -> QM31 { extension_from_raw_limbs(local_raw(input)) }

    fn external(state: [QM31; POSEIDON2_WIDTH]) -> [QM31; 4] {
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
            local_packed[group] = local(input);
            group += 1;
        }
        let sum = QM31::ZERO
            .add(local_packed[0])
            .add(local_packed[1])
            .add(local_packed[2])
            .add(local_packed[3]);
        local_packed.map(|value| value.add(sum))
    }

    fn m31_packed(
        mut state: [QM31; POSEIDON2_WIDTH],
        constants: [u32; POSEIDON2_WIDTH],
    ) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
        for lane in 0..POSEIDON2_WIDTH {
            state[lane].c0.a = state[lane].c0.a.add(M31(constants[lane]));
            state[lane] = pow5(state[lane]);
        }
        external(state)
    }

    fn leading(
        openings: &StateOnlyPoseidonOpenings,
    ) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
        let mut state = openings.z;
        for lane in 0..RATE {
            state[lane] = state[lane].add(openings.xor12_z[lane]);
        }
        external_linear_lazy(&mut state);
        m31_packed(
            full_round_m31_constants(state, EXTERNAL_INITIAL[0]),
            EXTERNAL_INITIAL[1],
        )
    }

    fn qm_packed(
        mut state: [QM31; POSEIDON2_WIDTH],
        constants: [QM31; POSEIDON2_WIDTH],
    ) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
        for lane in 0..POSEIDON2_WIDTH {
            state[lane] = pow5(state[lane].add(constants[lane]));
        }
        external(state)
    }

    fn full(
        state: [QM31; POSEIDON2_WIDTH],
        local: &[QM31; 16],
    ) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
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
        qm_packed(full_round(state, even), odd)
    }

    fn any_q() -> QM31 {
        let x: [u32;4] = kani::any::<[u32;4]>().map(|v| v & 0x7fff_ffff);
        kani::assume(x.iter().all(|v| *v < P));
        QM31 { c0: CM31::new(M31(x[0]),M31(x[1])), c1: CM31::new(M31(x[2]),M31(x[3])) }
    }
    fn any_state() -> [QM31;16] { core::array::from_fn(|_| any_q()) }

    fn assert_q(a:QM31,b:QM31) {
        assert_eq!(a.c0.a.0,b.c0.a.0); assert_eq!(a.c0.b.0,b.c0.b.0);
        assert_eq!(a.c1.a.0,b.c1.a.0); assert_eq!(a.c1.b.0,b.c1.b.0);
    }
    fn assert_packed(a:[QM31;4],b:[QM31;4]) {
        for j in 0..4 { assert_q(a[j],b[j]); }
    }
    fn assume_rows(input:[QM31;4]) {
        let t=rows(input);
        for r in 0..4 { for l in 0..4 { kani::assume(t[r][l] < 7*u64::from(P)); } }
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn external_group1_release() {
        let s=any_state();
        for g in 0..4 { assume_rows([s[4*g],s[4*g+1],s[4*g+2],s[4*g+3]]); }
        kani::cover!(true, "external group1 release domain inhabited");
        assert_q(external_linear_packed(s)[1],external(s)[1]);
    }

    #[kani::proof]
    #[kani::unwind(18)]
    fn external_group0() {
        let s=any_state();
        for g in 0..4 { assume_rows([s[4*g],s[4*g+1],s[4*g+2],s[4*g+3]]); }
        kani::cover!(true, "external group0 domain inhabited");
        assert_q(external_linear_packed(s)[0],external(s)[0]);
    }

    #[kani::proof]
    #[kani::unwind(6)]
    fn local_raw_all_bounded() {
        let input: [QM31;4]=core::array::from_fn(|_| any_q());
        assume_rows(input);
        kani::cover!(true, "complete raw domain inhabited");
        let a=external_local_packed_raw(input); let b=local_raw(input);
        for j in 0..4 { assert_eq!(a[j],b[j]); }
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn external_bounded() {
        let s=any_state();
        for g in 0..4 { assume_rows([s[4*g],s[4*g+1],s[4*g+2],s[4*g+3]]); }
        kani::cover!(true, "complete external domain inhabited");
        assert_packed(external_linear_packed(s),external(s));
    }

    #[kani::proof]
    #[kani::unwind(6)]
    fn local_raw_output2_bounded() {
        let input: [QM31;4] = core::array::from_fn(|_| any_q());
        let t = rows(input);
        for r in 0..4 { for l in 0..4 { kani::assume(t[r][l] < 7*u64::from(P)); } }
        kani::cover!(true, "derived raw2 bounds inhabited");
        let a = external_local_packed_raw(input); let b = local_raw(input);
        assert_eq!(a[2],b[2]);
    }

    #[kani::proof]
    #[kani::unwind(6)]
    fn local_raw_output1_bounded() {
        let input: [QM31;4] = core::array::from_fn(|_| any_q());
        // Redundant on canonical input: FJe_RawReference.row_bounds.
        let t = rows(input);
        for r in 0..4 { for l in 0..4 { kani::assume(t[r][l] < 7*u64::from(P)); } }
        kani::cover!(true, "derived row bounds inhabited");
        let a = external_local_packed_raw(input); let b = local_raw(input);
        assert_eq!(a[1],b[1]);
    }

    #[kani::proof]
    #[kani::unwind(6)]
    fn local_raw_output0() {
        let input: [QM31;4] = core::array::from_fn(|_| any_q());
        kani::cover!(true, "canonical raw output0 domain inhabited");
        let a = external_local_packed_raw(input); let b = local_raw(input);
        assert_eq!(a[0],b[0]);
    }

    #[kani::proof]
    #[kani::unwind(6)]
    fn local_raw_value() {
        let input: [QM31;4] = core::array::from_fn(|_| any_q());
        let a = external_local_packed_raw(input); let b = local_raw(input);
        assert_eq!(a[0],b[0]); assert_eq!(a[1],b[1]);
        assert_eq!(a[2],b[2]); assert_eq!(a[3],b[3]);
        kani::cover!(true, "canonical local inputs inhabited");
    }

    #[kani::proof]
    #[kani::unwind(18)]
    fn external_value() {
        let s = any_state();
        assert_packed(external_linear_packed(s),external(s));
        kani::cover!(true, "canonical external inputs inhabited");
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn leading_value() {
        let o = StateOnlyPoseidonOpenings {z:any_state(),succ_z:any_state(),xor12_z:any_state()};
        assert_packed(leading_pair_packed(&o),leading(&o));
        kani::cover!(true, "canonical leading inputs inhabited");
    }
    #[kani::proof]
    #[kani::unwind(18)]
    fn full_value() {
        let s = any_state(); let l = any_state();
        assert_packed(interpolated_full_pair_packed(s,&l),full(s,&l));
        kani::cover!(true, "canonical full inputs inhabited");
    }
}
