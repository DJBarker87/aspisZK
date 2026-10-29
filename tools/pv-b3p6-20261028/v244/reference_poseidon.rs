use crate::reference_field::{qm31_m31_dot,qm31_pack_base4,qm31_sum_products3_prepared,PreparedQm31Multiplier};
use aspis_core::field::{qm31_sum_products4,CM31,M31,P,QM31};
use aspis_statement::poseidon2::{POSEIDON2_WIDTH,RATE};
use aspis_statement::state_only_poseidon::{StateOnlyPoseidonOpenings,StateOnlyPoseidonSelectors,STATE_ONLY_POSEIDON_PACKED_LANES};
macro_rules! array4 { ($index:ident,$body:expr) => {{
    let mut output=[{let $index=0usize;$body},{let $index=1usize;$body},{let $index=2usize;$body},{let $index=3usize;$body}];
    output
}}; }
pub(crate) const EXTERNAL_INITIAL: [[u32; 16]; 4] = [
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
pub(crate) const EXTERNAL_FINAL: [[u32; 16]; 4] = [
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
pub(crate) const INTERNAL: [u32; 14] = [
    0x7f7ec4bf, 0x0421926f, 0x5198e669, 0x34db3148, 0x4368bafd, 0x66685c7f, 0x78d3249a, 0x60187881,
    0x76dad67a, 0x0690b437, 0x1ea95311, 0x40e5369a, 0x38f103fc, 0x1d226a21,
];
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}

#[inline(always)]
fn pow5(value: QM31) -> QM31 {
    let square = value.square();
    square.square().mul(value)
}

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

/// Addition-only Poseidon external layer with one reduction per output limb.
#[inline(never)]
fn external_linear_lazy(state:&mut[QM31;16]) {
    { let input=[state[0],state[1],state[2],state[3]];
      let output=external_group227(input);
      state[0]=output[0];
      state[1]=output[1];
      state[2]=output[2];
      state[3]=output[3];
    }
    { let input=[state[4],state[5],state[6],state[7]];
      let output=external_group227(input);
      state[4]=output[0];
      state[5]=output[1];
      state[6]=output[2];
      state[7]=output[3];
    }
    { let input=[state[8],state[9],state[10],state[11]];
      let output=external_group227(input);
      state[8]=output[0];
      state[9]=output[1];
      state[10]=output[2];
      state[11]=output[3];
    }
    { let input=[state[12],state[13],state[14],state[15]];
      let output=external_group227(input);
      state[12]=output[0];
      state[13]=output[1];
      state[14]=output[2];
      state[15]=output[3];
    }
    let sums=global_sums227(*state);
    state[0]=add_global227(state[0],sums[0]);
    state[1]=add_global227(state[1],sums[1]);
    state[2]=add_global227(state[2],sums[2]);
    state[3]=add_global227(state[3],sums[3]);
    state[4]=add_global227(state[4],sums[0]);
    state[5]=add_global227(state[5],sums[1]);
    state[6]=add_global227(state[6],sums[2]);
    state[7]=add_global227(state[7],sums[3]);
    state[8]=add_global227(state[8],sums[0]);
    state[9]=add_global227(state[9],sums[1]);
    state[10]=add_global227(state[10],sums[2]);
    state[11]=add_global227(state[11],sums[3]);
    state[12]=add_global227(state[12],sums[0]);
    state[13]=add_global227(state[13],sums[1]);
    state[14]=add_global227(state[14],sums[2]);
    state[15]=add_global227(state[15],sums[3]);
}

// Every row of the four-lane external matrix has coefficient sum seven.
// Canonical input limbs are below P, so every unreduced local output limb is
// strictly below this multiple of P. Multiples of this bound can therefore
// serve as zero-mod-P offsets for the signed tower-packing functionals.
const EXTERNAL_LOCAL_LIMB_MODULUS_BOUND: u64 = 7 * P as u64;
const _: () = assert!(8 * EXTERNAL_LOCAL_LIMB_MODULUS_BOUND < (1u64 << 62));

/// Apply the local external matrix and the tower-basis packing functional in
/// one raw-limb pass.
///
/// If `t[r,l] = sum_j B[r,j] * input[j,l]`, packing the four local outputs
/// against `(1, i, u, i*u)` gives exactly
///
/// ```text
/// c0.a = t[0,a] - t[1,b] + 2t[2,c] - t[2,d] - t[3,c] - 2t[3,d]
/// c0.b = t[0,b] + t[1,a] + t[2,c] + 2t[2,d] + 2t[3,c] - t[3,d]
/// c1.a = t[0,c] - t[1,d] + t[2,a] - t[3,b]
/// c1.b = t[0,d] + t[1,c] + t[2,b] + t[3,a]
/// ```
///
/// The signed offsets below are multiples of P and do not change the field
/// value. The first two raw outputs are below `56P`; the last two are below
/// `28P`. Thus one final reduction per output limb is sufficient.
#[inline(always)]
fn external_local_packed_raw(input: [QM31; 4]) -> [u64; 4] {
    let input = [extension_limbs(input[0]),extension_limbs(input[1]),extension_limbs(input[2]),extension_limbs(input[3])];
    let local: [[u64; 4]; 4] = array4!(output, {
        array4!(limb, {
            let a = u64::from(input[0][limb]);
            let b = u64::from(input[1][limb]);
            let c = u64::from(input[2][limb]);
            let d = u64::from(input[3][limb]);
            raw_limb227(output,a,b,c,d)
        })
    });
    let mut all_local_limbs_bounded = true;
    let mut output = 0usize;
    
        let mut limb = 0usize;
        
            all_local_limbs_bounded &= local[0usize][0usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[0usize][1usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[0usize][2usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[0usize][3usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        
        
    

        let mut limb = 0usize;
        
            all_local_limbs_bounded &= local[1usize][0usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[1usize][1usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[1usize][2usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[1usize][3usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        
        
    

        let mut limb = 0usize;
        
            all_local_limbs_bounded &= local[2usize][0usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[2usize][1usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[2usize][2usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[2usize][3usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        
        
    

        let mut limb = 0usize;
        
            all_local_limbs_bounded &= local[3usize][0usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[3usize][1usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[3usize][2usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        

            all_local_limbs_bounded &= local[3usize][3usize] < EXTERNAL_LOCAL_LIMB_MODULUS_BOUND;
            
        
        
    
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

/// Apply the final external layer only through the four tower-packed output
/// functionals consumed by the terminal composition.
///
/// If `B` is the four-lane local matrix and `J + I` is the global layer, then
/// packing commutes with both maps:
///
/// `pack((J + I) B x)_g = pack(B x_g) + sum_h pack(B x_h)`.
///
/// This is the transpose/adjoint form specialized to the fixed tower-basis
/// functional.  It avoids materializing and reducing all sixteen final lanes
/// and introduces no challenge-dependent dot products.
#[inline(never)]
fn external_linear_packed(state: [QM31; POSEIDON2_WIDTH]) -> [QM31; 4] {
    let mut local_packed = [QM31::ZERO; 4];
    let mut group = 0usize;
    
        let start = 4 * 0usize;
        let input = [
            state[start],
            state[start + 1],
            state[start + 2],
            state[start + 3],
        ];
        local_packed[0usize] = external_local_packed(input);
        
    

        let start = 4 * 1usize;
        let input = [
            state[start],
            state[start + 1],
            state[start + 2],
            state[start + 3],
        ];
        local_packed[1usize] = external_local_packed(input);
        
    

        let start = 4 * 2usize;
        let input = [
            state[start],
            state[start + 1],
            state[start + 2],
            state[start + 3],
        ];
        local_packed[2usize] = external_local_packed(input);
        
    

        let start = 4 * 3usize;
        let input = [
            state[start],
            state[start + 1],
            state[start + 2],
            state[start + 3],
        ];
        local_packed[3usize] = external_local_packed(input);
        
    
    let sum = QM31::ZERO
        .add(local_packed[0])
        .add(local_packed[1])
        .add(local_packed[2])
        .add(local_packed[3]);
    [local_packed[0].add(sum),local_packed[1].add(sum),local_packed[2].add(sum),local_packed[3].add(sum)]
}

#[inline(never)]
fn internal_linear_lazy(state:&mut[QM31;16]) {
    const SHIFTS:[u8;15]=[0,1,2,3,4,5,6,7,8,10,12,13,14,15,16];
    let old_zero=extension_limbs(state[0]);
    let mut part_sum=[0u64;4];
    part_sum=internal_sum227(part_sum,state[1]);
    part_sum=internal_sum227(part_sum,state[2]);
    part_sum=internal_sum227(part_sum,state[3]);
    part_sum=internal_sum227(part_sum,state[4]);
    part_sum=internal_sum227(part_sum,state[5]);
    part_sum=internal_sum227(part_sum,state[6]);
    part_sum=internal_sum227(part_sum,state[7]);
    part_sum=internal_sum227(part_sum,state[8]);
    part_sum=internal_sum227(part_sum,state[9]);
    part_sum=internal_sum227(part_sum,state[10]);
    part_sum=internal_sum227(part_sum,state[11]);
    part_sum=internal_sum227(part_sum,state[12]);
    part_sum=internal_sum227(part_sum,state[13]);
    part_sum=internal_sum227(part_sum,state[14]);
    part_sum=internal_sum227(part_sum,state[15]);
    let full_sum=internal_full_sum227(part_sum,old_zero);
    state[0]=internal_zero227(part_sum,old_zero);
    state[1]=internal_shift227(state[1],full_sum,SHIFTS[0]);
    state[2]=internal_shift227(state[2],full_sum,SHIFTS[1]);
    state[3]=internal_shift227(state[3],full_sum,SHIFTS[2]);
    state[4]=internal_shift227(state[4],full_sum,SHIFTS[3]);
    state[5]=internal_shift227(state[5],full_sum,SHIFTS[4]);
    state[6]=internal_shift227(state[6],full_sum,SHIFTS[5]);
    state[7]=internal_shift227(state[7],full_sum,SHIFTS[6]);
    state[8]=internal_shift227(state[8],full_sum,SHIFTS[7]);
    state[9]=internal_shift227(state[9],full_sum,SHIFTS[8]);
    state[10]=internal_shift227(state[10],full_sum,SHIFTS[9]);
    state[11]=internal_shift227(state[11],full_sum,SHIFTS[10]);
    state[12]=internal_shift227(state[12],full_sum,SHIFTS[11]);
    state[13]=internal_shift227(state[13],full_sum,SHIFTS[12]);
    state[14]=internal_shift227(state[14],full_sum,SHIFTS[13]);
    state[15]=internal_shift227(state[15],full_sum,SHIFTS[14]);
}

#[inline(never)]
fn full_round(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [QM31; POSEIDON2_WIDTH],
) -> [QM31; POSEIDON2_WIDTH] {
    
        state[0usize] = pow5(state[0usize].add(constants[0usize]));
    

        state[1usize] = pow5(state[1usize].add(constants[1usize]));
    

        state[2usize] = pow5(state[2usize].add(constants[2usize]));
    

        state[3usize] = pow5(state[3usize].add(constants[3usize]));
    

        state[4usize] = pow5(state[4usize].add(constants[4usize]));
    

        state[5usize] = pow5(state[5usize].add(constants[5usize]));
    

        state[6usize] = pow5(state[6usize].add(constants[6usize]));
    

        state[7usize] = pow5(state[7usize].add(constants[7usize]));
    

        state[8usize] = pow5(state[8usize].add(constants[8usize]));
    

        state[9usize] = pow5(state[9usize].add(constants[9usize]));
    

        state[10usize] = pow5(state[10usize].add(constants[10usize]));
    

        state[11usize] = pow5(state[11usize].add(constants[11usize]));
    

        state[12usize] = pow5(state[12usize].add(constants[12usize]));
    

        state[13usize] = pow5(state[13usize].add(constants[13usize]));
    

        state[14usize] = pow5(state[14usize].add(constants[14usize]));
    

        state[15usize] = pow5(state[15usize].add(constants[15usize]));
    
    external_linear_lazy(&mut state);
    state
}

/// Full round whose constants are pinned base-field values. Only c0.a changes
/// during the addition, avoiding three zero-limb additions per lane in the
/// two fixed leading rounds.
#[inline(never)]
fn full_round_m31_constants(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [u32; POSEIDON2_WIDTH],
) -> [QM31; POSEIDON2_WIDTH] {
    
        state[0usize].c0.a = state[0usize].c0.a.add(M31(constants[0usize]));
        state[0usize] = pow5(state[0usize]);
    

        state[1usize].c0.a = state[1usize].c0.a.add(M31(constants[1usize]));
        state[1usize] = pow5(state[1usize]);
    

        state[2usize].c0.a = state[2usize].c0.a.add(M31(constants[2usize]));
        state[2usize] = pow5(state[2usize]);
    

        state[3usize].c0.a = state[3usize].c0.a.add(M31(constants[3usize]));
        state[3usize] = pow5(state[3usize]);
    

        state[4usize].c0.a = state[4usize].c0.a.add(M31(constants[4usize]));
        state[4usize] = pow5(state[4usize]);
    

        state[5usize].c0.a = state[5usize].c0.a.add(M31(constants[5usize]));
        state[5usize] = pow5(state[5usize]);
    

        state[6usize].c0.a = state[6usize].c0.a.add(M31(constants[6usize]));
        state[6usize] = pow5(state[6usize]);
    

        state[7usize].c0.a = state[7usize].c0.a.add(M31(constants[7usize]));
        state[7usize] = pow5(state[7usize]);
    

        state[8usize].c0.a = state[8usize].c0.a.add(M31(constants[8usize]));
        state[8usize] = pow5(state[8usize]);
    

        state[9usize].c0.a = state[9usize].c0.a.add(M31(constants[9usize]));
        state[9usize] = pow5(state[9usize]);
    

        state[10usize].c0.a = state[10usize].c0.a.add(M31(constants[10usize]));
        state[10usize] = pow5(state[10usize]);
    

        state[11usize].c0.a = state[11usize].c0.a.add(M31(constants[11usize]));
        state[11usize] = pow5(state[11usize]);
    

        state[12usize].c0.a = state[12usize].c0.a.add(M31(constants[12usize]));
        state[12usize] = pow5(state[12usize]);
    

        state[13usize].c0.a = state[13usize].c0.a.add(M31(constants[13usize]));
        state[13usize] = pow5(state[13usize]);
    

        state[14usize].c0.a = state[14usize].c0.a.add(M31(constants[14usize]));
        state[14usize] = pow5(state[14usize]);
    

        state[15usize].c0.a = state[15usize].c0.a.add(M31(constants[15usize]));
        state[15usize] = pow5(state[15usize]);
    
    external_linear_lazy(&mut state);
    state
}

#[inline(never)]
fn full_round_packed(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [QM31; POSEIDON2_WIDTH],
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    
        state[0usize] = pow5(state[0usize].add(constants[0usize]));
    

        state[1usize] = pow5(state[1usize].add(constants[1usize]));
    

        state[2usize] = pow5(state[2usize].add(constants[2usize]));
    

        state[3usize] = pow5(state[3usize].add(constants[3usize]));
    

        state[4usize] = pow5(state[4usize].add(constants[4usize]));
    

        state[5usize] = pow5(state[5usize].add(constants[5usize]));
    

        state[6usize] = pow5(state[6usize].add(constants[6usize]));
    

        state[7usize] = pow5(state[7usize].add(constants[7usize]));
    

        state[8usize] = pow5(state[8usize].add(constants[8usize]));
    

        state[9usize] = pow5(state[9usize].add(constants[9usize]));
    

        state[10usize] = pow5(state[10usize].add(constants[10usize]));
    

        state[11usize] = pow5(state[11usize].add(constants[11usize]));
    

        state[12usize] = pow5(state[12usize].add(constants[12usize]));
    

        state[13usize] = pow5(state[13usize].add(constants[13usize]));
    

        state[14usize] = pow5(state[14usize].add(constants[14usize]));
    

        state[15usize] = pow5(state[15usize].add(constants[15usize]));
    
    external_linear_packed(state)
}

#[inline(never)]
fn full_round_m31_constants_packed(
    mut state: [QM31; POSEIDON2_WIDTH],
    constants: [u32; POSEIDON2_WIDTH],
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    
        state[0usize].c0.a = state[0usize].c0.a.add(M31(constants[0usize]));
        state[0usize] = pow5(state[0usize]);
    

        state[1usize].c0.a = state[1usize].c0.a.add(M31(constants[1usize]));
        state[1usize] = pow5(state[1usize]);
    

        state[2usize].c0.a = state[2usize].c0.a.add(M31(constants[2usize]));
        state[2usize] = pow5(state[2usize]);
    

        state[3usize].c0.a = state[3usize].c0.a.add(M31(constants[3usize]));
        state[3usize] = pow5(state[3usize]);
    

        state[4usize].c0.a = state[4usize].c0.a.add(M31(constants[4usize]));
        state[4usize] = pow5(state[4usize]);
    

        state[5usize].c0.a = state[5usize].c0.a.add(M31(constants[5usize]));
        state[5usize] = pow5(state[5usize]);
    

        state[6usize].c0.a = state[6usize].c0.a.add(M31(constants[6usize]));
        state[6usize] = pow5(state[6usize]);
    

        state[7usize].c0.a = state[7usize].c0.a.add(M31(constants[7usize]));
        state[7usize] = pow5(state[7usize]);
    

        state[8usize].c0.a = state[8usize].c0.a.add(M31(constants[8usize]));
        state[8usize] = pow5(state[8usize]);
    

        state[9usize].c0.a = state[9usize].c0.a.add(M31(constants[9usize]));
        state[9usize] = pow5(state[9usize]);
    

        state[10usize].c0.a = state[10usize].c0.a.add(M31(constants[10usize]));
        state[10usize] = pow5(state[10usize]);
    

        state[11usize].c0.a = state[11usize].c0.a.add(M31(constants[11usize]));
        state[11usize] = pow5(state[11usize]);
    

        state[12usize].c0.a = state[12usize].c0.a.add(M31(constants[12usize]));
        state[12usize] = pow5(state[12usize]);
    

        state[13usize].c0.a = state[13usize].c0.a.add(M31(constants[13usize]));
        state[13usize] = pow5(state[13usize]);
    

        state[14usize].c0.a = state[14usize].c0.a.add(M31(constants[14usize]));
        state[14usize] = pow5(state[14usize]);
    

        state[15usize].c0.a = state[15usize].c0.a.add(M31(constants[15usize]));
        state[15usize] = pow5(state[15usize]);
    
    external_linear_packed(state)
}

#[inline(never)]
fn internal_round(mut state: [QM31; POSEIDON2_WIDTH], constant: QM31) -> [QM31; 16] {
    state[0] = pow5(state[0].add(constant));
    internal_linear_lazy(&mut state);
    state
}

fn leading_pair(openings: &StateOnlyPoseidonOpenings) -> [QM31; POSEIDON2_WIDTH] {
    let mut state = openings.z;
    
        state[0usize] = state[0usize].add(openings.xor12_z[0usize]);
    

        state[1usize] = state[1usize].add(openings.xor12_z[1usize]);
    

        state[2usize] = state[2usize].add(openings.xor12_z[2usize]);
    

        state[3usize] = state[3usize].add(openings.xor12_z[3usize]);
    

        state[4usize] = state[4usize].add(openings.xor12_z[4usize]);
    

        state[5usize] = state[5usize].add(openings.xor12_z[5usize]);
    

        state[6usize] = state[6usize].add(openings.xor12_z[6usize]);
    

        state[7usize] = state[7usize].add(openings.xor12_z[7usize]);
    
    external_linear_lazy(&mut state);
    full_round_m31_constants(
        full_round_m31_constants(state, EXTERNAL_INITIAL[0]),
        EXTERNAL_INITIAL[1],
    )
}

fn leading_pair_packed(
    openings: &StateOnlyPoseidonOpenings,
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    let mut state = openings.z;
    
        state[0usize] = state[0usize].add(openings.xor12_z[0usize]);
    

        state[1usize] = state[1usize].add(openings.xor12_z[1usize]);
    

        state[2usize] = state[2usize].add(openings.xor12_z[2usize]);
    

        state[3usize] = state[3usize].add(openings.xor12_z[3usize]);
    

        state[4usize] = state[4usize].add(openings.xor12_z[4usize]);
    

        state[5usize] = state[5usize].add(openings.xor12_z[5usize]);
    

        state[6usize] = state[6usize].add(openings.xor12_z[6usize]);
    

        state[7usize] = state[7usize].add(openings.xor12_z[7usize]);
    
    external_linear_lazy(&mut state);
    full_round_m31_constants_packed(
        full_round_m31_constants(state, EXTERNAL_INITIAL[0]),
        EXTERNAL_INITIAL[1],
    )
}

#[inline(always)]
fn interpolate_three_constant_limb(
    weight0: u32,
    weight1: u32,
    weight2: u32,
    constant0: u32,
    constant1: u32,
    constant2: u32,
) -> M31 {
    M31::reduce_u64(
        u64::from(weight0) * u64::from(constant0)
            + u64::from(weight1) * u64::from(constant1)
            + u64::from(weight2) * u64::from(constant2),
    )
}

#[inline(always)]
fn interpolate_three_constant_columns(weights:[QM31;3],column0:[u32;16],column1:[u32;16],column2:[u32;16])->[QM31;16] {
    let mut output=[QM31::ZERO;16];
    output[0]=interpolate_column227(weights,column0[0],column1[0],column2[0]);
    output[1]=interpolate_column227(weights,column0[1],column1[1],column2[1]);
    output[2]=interpolate_column227(weights,column0[2],column1[2],column2[2]);
    output[3]=interpolate_column227(weights,column0[3],column1[3],column2[3]);
    output[4]=interpolate_column227(weights,column0[4],column1[4],column2[4]);
    output[5]=interpolate_column227(weights,column0[5],column1[5],column2[5]);
    output[6]=interpolate_column227(weights,column0[6],column1[6],column2[6]);
    output[7]=interpolate_column227(weights,column0[7],column1[7],column2[7]);
    output[8]=interpolate_column227(weights,column0[8],column1[8],column2[8]);
    output[9]=interpolate_column227(weights,column0[9],column1[9],column2[9]);
    output[10]=interpolate_column227(weights,column0[10],column1[10],column2[10]);
    output[11]=interpolate_column227(weights,column0[11],column1[11],column2[11]);
    output[12]=interpolate_column227(weights,column0[12],column1[12],column2[12]);
    output[13]=interpolate_column227(weights,column0[13],column1[13],column2[13]);
    output[14]=interpolate_column227(weights,column0[14],column1[14],column2[14]);
    output[15]=interpolate_column227(weights,column0[15],column1[15],column2[15]);
    output
}

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

fn interpolated_full_pair_packed(
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
    full_round_packed(full_round(state, even), odd)
}

fn interpolated_internal_pair(
    state: [QM31; POSEIDON2_WIDTH],
    local: &[QM31; 16],
) -> [QM31; POSEIDON2_WIDTH] {
    const ROWS: [usize; 7] = [2, 3, 4, 5, 6, 7, 8];
    let weights = [local[2usize],local[3usize],local[4usize],local[5usize],local[6usize],local[7usize],local[8usize]];
    let even_constants = [M31(INTERNAL[2 * (2usize - 2)]),M31(INTERNAL[2 * (3usize - 2)]),M31(INTERNAL[2 * (4usize - 2)]),M31(INTERNAL[2 * (5usize - 2)]),M31(INTERNAL[2 * (6usize - 2)]),M31(INTERNAL[2 * (7usize - 2)]),M31(INTERNAL[2 * (8usize - 2)])];
    let odd_constants = [M31(INTERNAL[2 * (2usize - 2) + 1]),M31(INTERNAL[2 * (3usize - 2) + 1]),M31(INTERNAL[2 * (4usize - 2) + 1]),M31(INTERNAL[2 * (5usize - 2) + 1]),M31(INTERNAL[2 * (6usize - 2) + 1]),M31(INTERNAL[2 * (7usize - 2) + 1]),M31(INTERNAL[2 * (8usize - 2) + 1])];
    let even = qm31_m31_dot(&weights, &even_constants);
    let odd = qm31_m31_dot(&weights, &odd_constants);
    internal_round(internal_round(state, even), odd)
}

/// Evaluate the four injectively packed successor-state constraints.
///
/// On an active Boolean row the result is zero exactly when the state at
/// `succ(z)` is the output of the row's two pinned Poseidon rounds (including
/// row zero's absorption and leading external layer).  No intermediate-round
/// state is constrained or committed.
#[inline(never)]
pub fn evaluate_state_only_poseidon_oracle(
    openings: &StateOnlyPoseidonOpenings,
    selectors: &StateOnlyPoseidonSelectors,
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    let leading_low = selectors.local[0];
    let full_low = QM31::ZERO.add(selectors.local[1]).add(selectors.local[9]).add(selectors.local[10]);
    let internal_low = QM31::ZERO.add(selectors.local[2]).add(selectors.local[3]).add(selectors.local[4]).add(selectors.local[5]).add(selectors.local[6]).add(selectors.local[7]).add(selectors.local[8]);
    let active_low = leading_low.add(full_low).add(internal_low);

    let leading = leading_pair(openings);
    let full = interpolated_full_pair(openings.z, &selectors.local);
    let internal = interpolated_internal_pair(openings.z, &selectors.local);
    let weights = [
        active_low,
        leading_low.neg(),
        full_low.neg(),
        internal_low.neg(),
    ];

    array4!(group, {
        let start = 4 * group;
        let target = qm31_pack_base4(&[openings.succ_z[start+0],openings.succ_z[start+1],openings.succ_z[start+2],openings.succ_z[start+3]]);
        let leading = qm31_pack_base4(&[leading[start+0],leading[start+1],leading[start+2],leading[start+3]]);
        let full = qm31_pack_base4(&[full[start+0],full[start+1],full[start+2],full[start+3]]);
        let internal = qm31_pack_base4(&[internal[start+0],internal[start+1],internal[start+2],internal[start+3]]);
        selectors.block.mul(qm31_sum_products4(
            [target, leading, full, internal],
            weights,
        ))
    })
}

/// Exact packed-projection implementation of [`evaluate_state_only_poseidon_oracle`].
///
/// Only the two full/full branches benefit: their second external layer is
/// consumed through its four packed adjoint functionals.  The internal branch
/// remains on the original path because a generic adjoint there would replace
/// additions by sixteen extension-field products.
#[inline(never)]
pub fn evaluate_state_only_poseidon_oracle_projected(
    openings: &StateOnlyPoseidonOpenings,
    selectors: &StateOnlyPoseidonSelectors,
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    let leading_low = selectors.local[0];
    let full_low = QM31::ZERO.add(selectors.local[1]).add(selectors.local[9]).add(selectors.local[10]);
    let internal_low = QM31::ZERO.add(selectors.local[2]).add(selectors.local[3]).add(selectors.local[4]).add(selectors.local[5]).add(selectors.local[6]).add(selectors.local[7]).add(selectors.local[8]);
    let leading = leading_pair_packed(openings);
    let full = interpolated_full_pair_packed(openings.z, &selectors.local);
    let internal = interpolated_internal_pair(openings.z, &selectors.local);
    let prepared_weights = [PreparedQm31Multiplier::new(leading_low),PreparedQm31Multiplier::new(full_low),PreparedQm31Multiplier::new(internal_low)];
    let prepared_block = PreparedQm31Multiplier::new(selectors.block);

    array4!(group, {
        let start = 4 * group;
        let target = qm31_pack_base4(&[openings.succ_z[start+0],openings.succ_z[start+1],openings.succ_z[start+2],openings.succ_z[start+3]]);
        let internal = qm31_pack_base4(&[internal[start+0],internal[start+1],internal[start+2],internal[start+3]]);
        // `active_low = leading_low + full_low + internal_low`, so the
        // four-product residual is exactly three weighted differences. This
        // removes one QM31 product per packed group without changing the
        // polynomial or its selector basis.
        prepared_block.mul(qm31_sum_products3_prepared(
            &prepared_weights,
            &[
                target.sub(leading[group]),
                target.sub(full[group]),
                target.sub(internal),
            ],
        ))
    })
}


fn raw_limb227(output:usize,a:u64,b:u64,c:u64,d:u64)->u64 {
    match output {0=>2*a+3*b+c+d,1=>a+2*b+3*c+d,2=>a+b+2*c+3*d,3=>3*a+b+c+2*d,_=>unreachable!()}
}

fn external_group227(state:[QM31;4])->[QM31;4] {
    let input=[extension_limbs(state[0]),extension_limbs(state[1]),extension_limbs(state[2]),extension_limbs(state[3])];
    [
    extension_from_raw_limbs([
      {let a=u64::from(input[0][0]); let b=u64::from(input[1][0]); let c=u64::from(input[2][0]); let d=u64::from(input[3][0]); raw_limb227(0,a,b,c,d)},
      {let a=u64::from(input[0][1]); let b=u64::from(input[1][1]); let c=u64::from(input[2][1]); let d=u64::from(input[3][1]); raw_limb227(0,a,b,c,d)},
      {let a=u64::from(input[0][2]); let b=u64::from(input[1][2]); let c=u64::from(input[2][2]); let d=u64::from(input[3][2]); raw_limb227(0,a,b,c,d)},
      {let a=u64::from(input[0][3]); let b=u64::from(input[1][3]); let c=u64::from(input[2][3]); let d=u64::from(input[3][3]); raw_limb227(0,a,b,c,d)},
    ]),
    extension_from_raw_limbs([
      {let a=u64::from(input[0][0]); let b=u64::from(input[1][0]); let c=u64::from(input[2][0]); let d=u64::from(input[3][0]); raw_limb227(1,a,b,c,d)},
      {let a=u64::from(input[0][1]); let b=u64::from(input[1][1]); let c=u64::from(input[2][1]); let d=u64::from(input[3][1]); raw_limb227(1,a,b,c,d)},
      {let a=u64::from(input[0][2]); let b=u64::from(input[1][2]); let c=u64::from(input[2][2]); let d=u64::from(input[3][2]); raw_limb227(1,a,b,c,d)},
      {let a=u64::from(input[0][3]); let b=u64::from(input[1][3]); let c=u64::from(input[2][3]); let d=u64::from(input[3][3]); raw_limb227(1,a,b,c,d)},
    ]),
    extension_from_raw_limbs([
      {let a=u64::from(input[0][0]); let b=u64::from(input[1][0]); let c=u64::from(input[2][0]); let d=u64::from(input[3][0]); raw_limb227(2,a,b,c,d)},
      {let a=u64::from(input[0][1]); let b=u64::from(input[1][1]); let c=u64::from(input[2][1]); let d=u64::from(input[3][1]); raw_limb227(2,a,b,c,d)},
      {let a=u64::from(input[0][2]); let b=u64::from(input[1][2]); let c=u64::from(input[2][2]); let d=u64::from(input[3][2]); raw_limb227(2,a,b,c,d)},
      {let a=u64::from(input[0][3]); let b=u64::from(input[1][3]); let c=u64::from(input[2][3]); let d=u64::from(input[3][3]); raw_limb227(2,a,b,c,d)},
    ]),
    extension_from_raw_limbs([
      {let a=u64::from(input[0][0]); let b=u64::from(input[1][0]); let c=u64::from(input[2][0]); let d=u64::from(input[3][0]); raw_limb227(3,a,b,c,d)},
      {let a=u64::from(input[0][1]); let b=u64::from(input[1][1]); let c=u64::from(input[2][1]); let d=u64::from(input[3][1]); raw_limb227(3,a,b,c,d)},
      {let a=u64::from(input[0][2]); let b=u64::from(input[1][2]); let c=u64::from(input[2][2]); let d=u64::from(input[3][2]); raw_limb227(3,a,b,c,d)},
      {let a=u64::from(input[0][3]); let b=u64::from(input[1][3]); let c=u64::from(input[2][3]); let d=u64::from(input[3][3]); raw_limb227(3,a,b,c,d)},
    ]),
    ]
}
fn global_sums227(state:[QM31;16])->[[u64;4];4] {
    [
    [u64::from(extension_limbs(state[0])[0]) + u64::from(extension_limbs(state[4])[0]) + u64::from(extension_limbs(state[8])[0]) + u64::from(extension_limbs(state[12])[0]),u64::from(extension_limbs(state[0])[1]) + u64::from(extension_limbs(state[4])[1]) + u64::from(extension_limbs(state[8])[1]) + u64::from(extension_limbs(state[12])[1]),u64::from(extension_limbs(state[0])[2]) + u64::from(extension_limbs(state[4])[2]) + u64::from(extension_limbs(state[8])[2]) + u64::from(extension_limbs(state[12])[2]),u64::from(extension_limbs(state[0])[3]) + u64::from(extension_limbs(state[4])[3]) + u64::from(extension_limbs(state[8])[3]) + u64::from(extension_limbs(state[12])[3])],
    [u64::from(extension_limbs(state[1])[0]) + u64::from(extension_limbs(state[5])[0]) + u64::from(extension_limbs(state[9])[0]) + u64::from(extension_limbs(state[13])[0]),u64::from(extension_limbs(state[1])[1]) + u64::from(extension_limbs(state[5])[1]) + u64::from(extension_limbs(state[9])[1]) + u64::from(extension_limbs(state[13])[1]),u64::from(extension_limbs(state[1])[2]) + u64::from(extension_limbs(state[5])[2]) + u64::from(extension_limbs(state[9])[2]) + u64::from(extension_limbs(state[13])[2]),u64::from(extension_limbs(state[1])[3]) + u64::from(extension_limbs(state[5])[3]) + u64::from(extension_limbs(state[9])[3]) + u64::from(extension_limbs(state[13])[3])],
    [u64::from(extension_limbs(state[2])[0]) + u64::from(extension_limbs(state[6])[0]) + u64::from(extension_limbs(state[10])[0]) + u64::from(extension_limbs(state[14])[0]),u64::from(extension_limbs(state[2])[1]) + u64::from(extension_limbs(state[6])[1]) + u64::from(extension_limbs(state[10])[1]) + u64::from(extension_limbs(state[14])[1]),u64::from(extension_limbs(state[2])[2]) + u64::from(extension_limbs(state[6])[2]) + u64::from(extension_limbs(state[10])[2]) + u64::from(extension_limbs(state[14])[2]),u64::from(extension_limbs(state[2])[3]) + u64::from(extension_limbs(state[6])[3]) + u64::from(extension_limbs(state[10])[3]) + u64::from(extension_limbs(state[14])[3])],
    [u64::from(extension_limbs(state[3])[0]) + u64::from(extension_limbs(state[7])[0]) + u64::from(extension_limbs(state[11])[0]) + u64::from(extension_limbs(state[15])[0]),u64::from(extension_limbs(state[3])[1]) + u64::from(extension_limbs(state[7])[1]) + u64::from(extension_limbs(state[11])[1]) + u64::from(extension_limbs(state[15])[1]),u64::from(extension_limbs(state[3])[2]) + u64::from(extension_limbs(state[7])[2]) + u64::from(extension_limbs(state[11])[2]) + u64::from(extension_limbs(state[15])[2]),u64::from(extension_limbs(state[3])[3]) + u64::from(extension_limbs(state[7])[3]) + u64::from(extension_limbs(state[11])[3]) + u64::from(extension_limbs(state[15])[3])],
    ]
}
fn add_global227(value:QM31,sums:[u64;4])->QM31 {
    let limbs=extension_limbs(value);
    extension_from_raw_limbs([u64::from(limbs[0])+sums[0],u64::from(limbs[1])+sums[1],u64::from(limbs[2])+sums[2],u64::from(limbs[3])+sums[3]])
}

fn interpolate_column227(weights:[QM31;3],column0:u32,column1:u32,column2:u32)->QM31 {
QM31 {
            c0: CM31::new(
                interpolate_three_constant_limb(
                    weights[0].c0.a.0,
                    weights[1].c0.a.0,
                    weights[2].c0.a.0,
                    column0,
                    column1,
                    column2,
                ),
                interpolate_three_constant_limb(
                    weights[0].c0.b.0,
                    weights[1].c0.b.0,
                    weights[2].c0.b.0,
                    column0,
                    column1,
                    column2,
                ),
            ),
            c1: CM31::new(
                interpolate_three_constant_limb(
                    weights[0].c1.a.0,
                    weights[1].c1.a.0,
                    weights[2].c1.a.0,
                    column0,
                    column1,
                    column2,
                ),
                interpolate_three_constant_limb(
                    weights[0].c1.b.0,
                    weights[1].c1.b.0,
                    weights[2].c1.b.0,
                    column0,
                    column1,
                    column2,
                ),
            ),
        }
}

fn internal_sum227(mut part_sum:[u64;4],value:QM31)->[u64;4] {
    let limbs=extension_limbs(value);
    part_sum[0]+=u64::from(limbs[0]);
    part_sum[1]+=u64::from(limbs[1]);
    part_sum[2]+=u64::from(limbs[2]);
    part_sum[3]+=u64::from(limbs[3]);
    part_sum
}
fn internal_full_sum227(part_sum:[u64;4],old_zero:[u32;4])->[u64;4] {
    [part_sum[0]+u64::from(old_zero[0]),part_sum[1]+u64::from(old_zero[1]),part_sum[2]+u64::from(old_zero[2]),part_sum[3]+u64::from(old_zero[3])]
}
fn internal_zero227(part_sum:[u64;4],old_zero:[u32;4])->QM31 {
    extension_from_raw_limbs([part_sum[0]+u64::from(P)-u64::from(old_zero[0]),part_sum[1]+u64::from(P)-u64::from(old_zero[1]),part_sum[2]+u64::from(P)-u64::from(old_zero[2]),part_sum[3]+u64::from(P)-u64::from(old_zero[3])])
}
fn internal_shift227(value:QM31,full_sum:[u64;4],shift:u8)->QM31 {
    let limbs=extension_limbs(value);
    extension_from_raw_limbs([full_sum[0]+(u64::from(limbs[0])<<shift),full_sum[1]+(u64::from(limbs[1])<<shift),full_sum[2]+(u64::from(limbs[2])<<shift),full_sum[3]+(u64::from(limbs[3])<<shift)])
}
