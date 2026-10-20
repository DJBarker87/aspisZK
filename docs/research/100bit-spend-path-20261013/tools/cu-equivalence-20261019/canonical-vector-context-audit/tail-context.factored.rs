pub fn four_dots(q: &[u8], g: &[WideExact; 29]) -> [WideExact; 4] {
    core::array::from_fn(|slot| {
        let mut limbs = [0u64; WideExact::LIMB_COUNT];
        for start in (0..26).step_by(4) {
            let mut sums = [0u64; WideExact::LIMB_COUNT];
            for term in start..core::cmp::min(start + 4, 26) {
                let scalar = M31::from_le_bytes(
                    q[slot * 120 + term * 4..slot * 120 + term * 4 + 4]
                        .try_into()
                        .unwrap(),
                )
                .unwrap();
                let coefficient = g[term].to_limbs();
                for limb in 0..WideExact::LIMB_COUNT {
                    sums[limb] += u64::from(coefficient[limb]) * u64::from(scalar.0);
                }
            }
            for limb in 0..WideExact::LIMB_COUNT {
                limbs[limb] += (sums[limb] & 0x7fff_ffff) + (sums[limb] >> 31);
            }
        }

        let mut value = WideExact::from_limbs(core::array::from_fn(|i| M31::reduce_u64(limbs[i]).0)).unwrap();
        value.add(SOURCE_TAIL(q,g,slot))
    })
}