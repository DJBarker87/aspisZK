#![cfg(feature = "r0-probe-reference")]
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

#[test]
#[cfg(feature = "r0-cost-probe")]
fn r91_add_sub_and_raw_outcomes() {
    use aspis_core::{field::M31, r0_probe::equality_trace};
    assert!(cfg!(feature = "r0"));
    let mut seed = 0x91_20261009u64;
    for _ in 0..1_000_000 {
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            M31((seed % u64::from(P)) as u32)
        };
        let (a, b) = (next(), next());
        let actual = (a.add(b), a.sub(b));
        let _reference = equality_trace::reference();
        assert_eq!(actual, (a.add(b), a.sub(b)));
        assert_eq!(
            actual.0 .0,
            ((u64::from(a.0) + u64::from(b.0)) % u64::from(P)) as u32
        );
        assert_eq!(
            actual.1 .0,
            ((u64::from(a.0) + u64::from(P) - u64::from(b.0)) % u64::from(P)) as u32
        );
    }
    for a in [
        0,
        1,
        P - 1,
        P,
        P + 1,
        u32::MAX / 2 + 2,
        u32::MAX - 1,
        u32::MAX,
    ] {
        for b in [
            0,
            1,
            P - 1,
            P,
            P + 1,
            u32::MAX / 2 + 2,
            u32::MAX - 1,
            u32::MAX,
        ] {
            for sub in [false, true] {
                let operation = || {
                    if sub {
                        M31(a).sub(M31(b))
                    } else {
                        M31(a).add(M31(b))
                    }
                };
                let actual = std::panic::catch_unwind(operation);
                let _reference = equality_trace::reference();
                let expected = std::panic::catch_unwind(operation);
                match (actual, expected) {
                    (Ok(a), Ok(b)) => assert_eq!(a, b),
                    (Err(_), Err(_)) => (),
                    _ => panic!("R91 raw outcome changed"),
                }
            }
        }
    }
    eprintln!("PASS: R91 million canonical add/sub pairs and 128 raw outcomes equal frozen R-E3 and independent modular arithmetic");
}

#[test]
fn r60_chain_equals_binary_exponent() {
    use aspis_core::field::M31;
    for x in (1..=4096).chain([P - 2, P - 1]) {
        assert_eq!(M31(x).inv(), M31(x).pow(u64::from(P - 2)));
    }
    eprintln!("PASS: retained R60 inverse chain equals exponent P-2 on 4098 inputs");
}
