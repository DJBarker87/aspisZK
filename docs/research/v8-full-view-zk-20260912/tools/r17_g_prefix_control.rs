// Focused controls for the experimental sparse-permutation G prefix.
// Include this beside the staged `r17_fast_g` module.
#[cfg(not(performance_sbf))]
pub(super) fn check() {
    use super::super::corelib::field::{CM31, M31, QM31 as K};
    const PREFIX: usize = 479;
    super::fast_g::check_fft1024();

    let make = |case: usize| -> [K; 271] {
        core::array::from_fn(|i| {
            let x = match case {
                0 => 0,
                1 => 2_147_483_646,
                2 => (i == 0) as u32,
                3 => (i == 270) as u32,
                _ => ((i as u32) * 97 + (case as u32) * 83) % 2_147_483_647,
            };
            // Deliberately unequal extension components exercise both lanes.
            K {
                c0: CM31::new(M31(x), M31((x + i as u32 + 1) % 2_147_483_647)),
                c1: CM31::new(
                    M31((x + 17) % 2_147_483_647),
                    M31((x + 2 * i as u32 + 3) % 2_147_483_647),
                ),
            }
        })
    };
    for case in 0..6 {
        let coins = make(case);
        let before = coins;
        let mut full = vec![K::ZERO; 1024];
        let mut pref = vec![
            K {
                c0: CM31::ONE,
                c1: CM31::ONE,
            };
            1024
        ];
        super::fast_g::apply(&coins, full.as_mut_slice().try_into().unwrap());
        super::fast_g::prefix_into(&coins, pref.as_mut_slice().try_into().unwrap());
        assert_eq!(super::fast_g::pivot(&coins),full[1023]);
        assert_eq!(
            coins, before,
            "prefix must not mutate input (no-alias control)"
        );
        for j in 0..PREFIX {
            assert_eq!(pref[j], full[j], "arbitrary case {case}, index {j}");
        }
    }
    // Every one of the 271 basis vectors, including both endpoints.
    for basis in 0..271 {
        let mut coins = [K::ZERO; 271];
        coins[basis] = K {
            c0: CM31::new(M31(1), M31(2)),
            c1: CM31::new(M31(3), M31(5)),
        };
        let mut full = vec![K::ZERO; 1024];
        let mut pref = vec![
            K {
                c0: CM31::ONE,
                c1: CM31::ONE,
            };
            1024
        ];
        super::fast_g::apply(&coins, full.as_mut_slice().try_into().unwrap());
        super::fast_g::prefix_into(&coins, pref.as_mut_slice().try_into().unwrap());
        assert_eq!(super::fast_g::pivot(&coins),full[1023]);
        for j in 0..PREFIX {
            assert_eq!(pref[j], full[j], "basis {basis}, index {j}");
        }
    }
    println!("PASS: 6 arbitrary unequal-lane vectors and all 271 basis vectors agree on G prefix 0..478; root/normalization/no-alias controls pass");
}
