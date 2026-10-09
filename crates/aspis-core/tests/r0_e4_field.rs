#![cfg(feature = "r0-e4-reference")]
use aspis_core::field::{WideExact as E, P};
#[test]
fn karatsuba_million_pairs_and_all_limb_units() {
    assert!(!cfg!(debug_assertions), "optimized equality gate required");
    let mut seed = 0x726534_20261009u64;
    let mut next = || {
        E::from_limbs(core::array::from_fn(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % u64::from(P)) as u32
        }))
        .unwrap()
    };
    for i in 0..1_000_000 {
        let (a, b) = (next(), next());
        assert_eq!(
            a.mul(b).to_le_bytes(),
            a.mul_re3(b).to_le_bytes(),
            "pair {i}"
        );
    }
    let unit = |i| {
        let mut limbs = [0; 8];
        limbs[i] = 1;
        E::from_limbs(limbs).unwrap()
    };
    for i in 0..8 {
        for j in 0..8 {
            assert_eq!(
                unit(i).mul(unit(j)).to_le_bytes(),
                unit(i).mul_re3(unit(j)).to_le_bytes()
            );
        }
    }
    for a in [E::ZERO, E::ONE, E::from_limbs([P - 1; 8]).unwrap()] {
        for b in [E::ZERO, E::ONE, E::from_limbs([P - 1; 8]).unwrap()] {
            assert_eq!(a.mul(b).to_le_bytes(), a.mul_re3(b).to_le_bytes());
        }
    }
    eprintln!("PASS: 1000000 deterministic random pairs, 64 limb-unit pairs, 9 boundary pairs; bitwise equality with frozen R-E3 schoolbook");
}
