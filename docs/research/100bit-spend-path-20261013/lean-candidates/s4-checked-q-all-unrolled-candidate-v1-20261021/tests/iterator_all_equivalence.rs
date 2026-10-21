const P: u32 = 0x7fff_ffff;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Q([u32; 4]);

fn reference_from_limbs(x: [u32; 4]) -> Option<Q> {
    if x.iter().all(|&v| v < P) { Some(Q(x)) } else { None }
}

fn candidate_from_limbs(x: [u32; 4]) -> Option<Q> {
    let [a, b, c, d] = x;
    if a < P && b < P && c < P && d < P {
        Some(Q([a, b, c, d]))
    } else {
        None
    }
}

#[test]
fn exhaustive_predicate_partition_and_boundaries() {
    // The validation predicate has exactly two input classes per limb.  The
    // 16 tuples cover every truth assignment across all four ordered checks.
    for mask in 0u32..16 {
        let x = core::array::from_fn(|i| if (mask >> i) & 1 == 0 { P - 1 } else { P });
        assert_eq!(reference_from_limbs(x), candidate_from_limbs(x), "mask={mask}");
    }
    // Include the lower boundary, values just around P, and maximal u32 in
    // every position, with the other three coordinates valid.
    for i in 0..4 {
        for v in [0, 1, P - 1, P, P + 1, u32::MAX] {
            let mut x = [P - 1; 4];
            x[i] = v;
            assert_eq!(reference_from_limbs(x), candidate_from_limbs(x), "i={i}, v={v}");
        }
    }
}

#[test]
fn deterministic_arbitrary_array_differential() {
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    for _ in 0..250_000 {
        let mut x = [0u32; 4];
        for limb in &mut x {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            *limb = (state >> 16) as u32;
        }
        assert_eq!(reference_from_limbs(x), candidate_from_limbs(x), "x={x:?}");
    }
}
