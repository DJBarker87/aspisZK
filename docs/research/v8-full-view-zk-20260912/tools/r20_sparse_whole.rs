//! Source-local sequential sparse G terminal using the R20 whole-dot helper.
//!
//! The retained R18 terminal remains the reference.  This candidate processes
//! one code group at a time, keeping only six normal coefficients and the
//! sixteen derived final values on the stack; the coin operands remain a
//! contiguous caller slice and all substantial storage remains
//! caller-owned `sums`.
use super::{corelib, r20_whole_dot};
use corelib::field::QM31 as K;

pub const N: usize = 1024;
pub const COINS: usize = 271;

#[inline]
pub const fn slot(i: usize) -> usize {
    128 + 3 * i
}

/// Same signature and coordinate map as the retained R18 sparse terminal.
/// Inputs must satisfy the actual source's canonical QM31 boundary contract.
pub fn sparse_terminal(
    coins: &[K],
    normal: &[K],
    carry: &[K],
    high: &[K],
    sums: &mut [K],
) -> [K; 4] {
    assert!(coins.len() >= COINS && normal.len() >= 16 && carry.len() >= 3);
    assert!(high.len() >= 16 && sums.len() >= 128);
    sums[..128].fill(K::ZERO);

    let mut coin_index = 0usize;
    for group in 0..64 {
        let mut group_normal = [K::ZERO; 6];
        let mut group_carry = K::ZERO;
        let mut count = 0usize;
        let group_start = coin_index;
        while coin_index < COINS {
            let row = slot(coin_index);
            if row >> 4 != group {
                break;
            }
            assert!(count < 6, "sparse group exceeds six selected coins");
            let low = row & 15;
            group_normal[count] = normal[low];
            if low < 3 {
                group_carry = group_carry.add(coins[coin_index].mul(carry[low]));
            }
            count += 1;
            coin_index += 1;
        }
        sums[2 * group] = if count == 0 {
            K::ZERO
        } else {
            r20_whole_dot::dot(&coins[group_start..coin_index], &group_normal[..count])
                .expect("canonical sparse normal operands")
        };
        sums[2 * group + 1] = group_carry;
    }
    assert_eq!(coin_index, COINS);

    let mut out = [K::ZERO; 4];
    for group in 0..4 {
        let mut values = [K::ZERO; 16];
        for lane in 0..16 {
            let j: usize = group * 16 + lane;
            let mut bits = j.trailing_ones() as usize;
            let mut value = if j + 1 < 64 {
                sums[2 * (j + 1) + 1]
            } else {
                K::ZERO
            };
            while bits != 0 {
                bits -= 1;
                let row = j & !((1usize << (bits + 1)) - 1);
                value = value.add(sums[2 * row + 1]).half();
            }
            values[lane] = value.add(sums[2 * j]);
        }
        out[group] =
            r20_whole_dot::dot(&high[..16], &values).expect("canonical sparse high operands");
    }
    for value in &mut out {
        for _ in 0..8 {
            *value = value.half();
        }
    }
    out
}

#[inline(always)]
fn sample(n: u32) -> K {
    use corelib::field::{CM31, M31, P};
    let q = |v: u32| M31(v % P);
    K {
        c0: CM31::new(q(n), q(n.wrapping_mul(3).wrapping_add(7))),
        c1: CM31::new(
            q(n.wrapping_mul(5).wrapping_add(11)),
            q(n.wrapping_mul(7).wrapping_add(13)),
        ),
    }
}

#[inline(always)]
fn all_max() -> K {
    use corelib::field::{CM31, M31, P};
    let p = M31(P - 1);
    K {
        c0: CM31::new(p, p),
        c1: CM31::new(p, p),
    }
}

/// Differential hook for a research harness.  The caller supplies the actual
/// retained R18 `sparse_terminal`; this function does not replace or weaken it.
/// It checks every one-hot 271-coin basis and 24 arbitrary full inputs,
/// including zero/one/maximal canonical controls.
pub fn differential_check(reference: fn(&[K], &[K], &[K], &[K], &mut [K]) -> [K; 4]) {
    for case in 0..(COINS + 24) {
        let mut coins = [K::ZERO; COINS];
        if case < COINS {
            coins[case] = K::ONE;
        } else if case == COINS {
            coins.fill(K::ZERO);
        } else if case == COINS + 1 {
            coins.fill(K::ONE);
        } else if case == COINS + 2 {
            coins.fill(all_max());
        } else {
            for (i, value) in coins.iter_mut().enumerate() {
                *value = sample((case as u32).wrapping_mul(101).wrapping_add(i as u32));
            }
        }
        let mut normal = [K::ZERO; 16];
        let mut carry = [K::ZERO; 3];
        let mut high = [K::ZERO; 16];
        if case == COINS {
            normal.fill(K::ZERO);
            carry.fill(K::ZERO);
            high.fill(K::ZERO);
        } else if case == COINS + 1 {
            normal.fill(K::ONE);
            carry.fill(K::ONE);
            high.fill(K::ONE);
        } else if case == COINS + 2 {
            normal.fill(all_max());
            carry.fill(all_max());
            high.fill(all_max());
        } else {
            for (i, value) in normal.iter_mut().enumerate() {
                *value = sample(10_001 + case as u32 * 17 + i as u32);
            }
            for (i, value) in carry.iter_mut().enumerate() {
                *value = sample(20_001 + case as u32 * 19 + i as u32);
            }
            for (i, value) in high.iter_mut().enumerate() {
                *value = sample(30_001 + case as u32 * 23 + i as u32);
            }
        }
        let mut expected_sums = [K::ZERO; 128];
        let mut actual_sums = [K::ZERO; 128];
        let expected = reference(&coins, &normal, &carry, &high, &mut expected_sums);
        let actual = sparse_terminal(&coins, &normal, &carry, &high, &mut actual_sums);
        assert_eq!(actual, expected, "sparse whole case {case}");
        assert_eq!(actual_sums, expected_sums, "sparse sums case {case}");
    }
}
