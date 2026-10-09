//! Complete linear-map comparison on unit vectors, plus dense random vectors.
use aspis_core::{
    field::{WideExact as E, M31},
    r0::{
        basis::{BasisSize, NaturalBasis},
        chord::{self, Secant},
        structured,
    },
};
fn main() {
    assert!(!cfg!(debug_assertions));
    let start = std::time::Instant::now();
    let basis = NaturalBasis::new(BasisSize::Initial).unwrap();
    for j in 0..512 {
        assert_eq!(
            structured::top_rows(j),
            [basis.matrix()[510 * 512 + j], basis.matrix()[511 * 512 + j]],
            "row {j}"
        );
    }
    let mut seed = 0x726532_20261009u64;
    fn random(seed: &mut u64) -> E {
        let limbs = core::array::from_fn(|_| {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            (*seed % 2_147_483_647) as u32
        });
        E::from_limbs(limbs).unwrap()
    }
    let lines = [
        Secant {
            a: E::ONE,
            b: E::ONE,
            c: E::ONE,
        },
        Secant {
            a: E::ZERO,
            b: E::ONE,
            c: E::ZERO,
        },
        Secant {
            a: E::ZERO,
            b: E::ZERO,
            c: E::ONE,
        },
        Secant {
            a: random(&mut seed),
            b: random(&mut seed),
            c: random(&mut seed),
        },
    ];
    let mut even = vec![E::ZERO; 512];
    let mut odd = even.clone();
    let mut twice = even.clone();
    for (l, line) in lines.into_iter().enumerate() {
        let mut input = [E::ZERO; 1024];
        for j in 0..1024 {
            input[j] = E::ONE;
            let expected = chord::quotient_weights(&basis, line, &input).unwrap();
            let mut actual = input.to_vec();
            structured::quotient_weights(line, &mut actual, &mut even, &mut odd, &mut twice)
                .unwrap();
            assert_eq!(actual, expected, "unit vector {j}, line {l}");
            input[j] = E::ZERO;
        }
        for trial in 0..8 {
            for x in &mut input {
                *x = random(&mut seed);
            }
            let expected = chord::quotient_weights(&basis, line, &input).unwrap();
            let mut actual = input.to_vec();
            structured::quotient_weights(line, &mut actual, &mut even, &mut odd, &mut twice)
                .unwrap();
            assert_eq!(actual, expected, "random {trial}, line {l}");
        }
        println!(
            "line {l}: all 1024 unit vectors and 8 random vectors agree; elapsed {:?}",
            start.elapsed()
        );
    }
    println!(
        "PASS: 4096 unit vectors, 32 random vectors, rows 510/511 at all 512 columns; {:?}",
        start.elapsed()
    );
    let _ = M31::ONE;
}
