//! Standalone source checker for the R20 private canonical arithmetic packet.
//!
//! This is a comparison harness only. It does not alter `aspis_core` or the
//! public M31/QM31 APIs. The parent release job should compile/run it in an
//! optimized profile after wiring the packet's actual crate dependency.

#[path = "r20_private_canonical.rs"]
mod canonical;

use aspis_core::field::{CM31, M31, QM31};
use canonical::{P, Q};

const VECTORS: usize = 200_000;

fn actual(limbs: [u32; 4]) -> QM31 {
    QM31 {
        c0: CM31::new(M31(limbs[0]), M31(limbs[1])),
        c1: CM31::new(M31(limbs[2]), M31(limbs[3])),
    }
}

fn next_limb(state: &mut u64) -> u32 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    (*state % u64::from(P)) as u32
}

fn vectors() -> Vec<[u32; 4]> {
    let mut out = Vec::with_capacity(VECTORS);
    out.push([0, 0, 0, 0]);
    out.push([1, 0, 0, 0]);
    out.push([P - 1, P - 1, P - 1, P - 1]);
    let mut state = 0x5242_305f_6669_656c_u64;
    while out.len() < VECTORS {
        out.push(core::array::from_fn(|_| next_limb(&mut state)));
    }
    out
}

fn check_invalid_construction() {
    for limb in 0..4 {
        for invalid in [P, P + 1, u32::MAX] {
            let mut candidate = [0; 4];
            candidate[limb] = invalid;
            assert!(
                Q::from_limbs(candidate).is_none(),
                "accepted invalid limb {limb}={invalid}"
            );
        }
    }
    assert!(Q::from_m31(P).is_none());
    assert!(Q::from_m31(u32::MAX).is_none());
}

fn check_reducer_edges() {
    for value in [u64::MAX, (1u64 << 62) - 1] {
        assert_eq!(canonical::reduce(value), M31::reduce_u64(value).0);
    }
}

pub fn run() {
    check_invalid_construction();
    check_reducer_edges();
    let values = vectors();
    for (index, &left_limbs) in values.iter().enumerate() {
        let right_limbs = if index < 3 {
            left_limbs
        } else {
            values[VECTORS - 1 - index]
        };
        let left = Q::from_limbs(left_limbs).unwrap();
        let right = Q::from_limbs(right_limbs).unwrap();
        let left_actual = actual(left_limbs);
        let right_actual = actual(right_limbs);

        assert_eq!(
            left.add(right).limbs(),
            limbs(left_actual.add(right_actual))
        );
        assert_eq!(
            left.sub(right).limbs(),
            limbs(left_actual.sub(right_actual))
        );
        assert_eq!(
            left.mul(right).limbs(),
            limbs(left_actual.mul(right_actual))
        );

        let scalar = left_limbs[index & 3];
        assert_eq!(
            left.mul_m31(scalar).unwrap().limbs(),
            limbs(left_actual.mul_m31(M31(scalar))),
        );

        let mut repeated = left_actual;
        for n in 0..=30 {
            assert_eq!(left.half_pow(n).unwrap().limbs(), limbs(repeated));
            repeated = repeated.half();
        }
        assert!(left.half_pow(31).is_none());
        assert_eq!(left.half().limbs(), limbs(left_actual.half()));
    }
    println!("R20_PRIVATE_FIELD_CHECK vectors={VECTORS} invalid_limb_positions=4 invalid_values=3 half_powers=31 reducer_edges=2");
}

fn limbs(value: QM31) -> [u32; 4] {
    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
}

fn main() {
    run();
}
