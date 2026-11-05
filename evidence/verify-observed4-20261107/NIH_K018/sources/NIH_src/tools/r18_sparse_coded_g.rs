// R18 sparse code-coordinate G candidate; research/tooling only.
// No production caller, transcript, profile, or security premise is changed.
use super::corelib::field::{qm31_sum_products4, M31, M31_HALF, QM31 as K};

pub const N: usize = 1024;
pub const COINS: usize = 271;
pub const REST: usize = 752;

#[inline]
pub const fn slot(i: usize) -> usize {
    128 + 3 * i
}

pub fn mixed_coins_into(g: &[K], order: &[usize; N], out: &mut [K]) {
    assert!(g.len() >= N && out.len() >= COINS);
    for i in 0..COINS {
        out[i] = g[order[slot(i)]];
    }
}

pub fn coin_weights_into(point: &[K], out: &mut [K]) {
    assert!(point.len() >= 10 && out.len() >= COINS);
    // Fixed public powers of one-half live in M31, not the full extension.
    // This preserves every coefficient while using four scalar limb products.
    let mut scale = M31::ONE;
    for r in (0..10).rev() {
        let start = 1 + 27 * r;
        let x = point[r];
        out[start] = K::ONE.sub(x.add(x)).mul_m31(scale);
        let mut power = x.square();
        for i in 1..27 {
            out[start + i] = power.sub(x).mul_m31(scale);
            power = power.mul(x);
        }
        scale = scale.mul(M31_HALF);
    }
    out[0] = K::ONE.mul_m31(scale);
}

pub fn original_weights_into(point: &[K], order: &[usize; N], coins: &mut [K], out: &mut [K]) {
    assert!(coins.len() >= COINS && out.len() >= N);
    coin_weights_into(point, coins);
    out[..N].fill(K::ZERO);
    for i in 0..COINS {
        out[order[slot(i)]] = coins[i];
    }
}

pub fn code_weights_into(point: &[K], coins: &mut [K], out: &mut [K]) {
    assert!(coins.len() >= COINS && out.len() >= N);
    coin_weights_into(point, coins);
    out[..N].fill(K::ZERO);
    for i in 0..COINS {
        out[slot(i)] = coins[i];
    }
}

pub fn split(c: &[K], coins: &mut [K], rest: &mut [K]) -> bool {
    assert!(c.len() >= N && coins.len() >= COINS && rest.len() >= REST);
    if c[1023] != K::ZERO {
        return false;
    }
    for i in 0..COINS {
        coins[i] = c[slot(i)];
    }
    let mut at = 0;
    for j in 0..1023 {
        let selected = j >= 128 && j <= 938 && (j - 128) % 3 == 0;
        if !selected {
            rest[at] = c[j];
            at += 1;
        }
    }
    at == REST
}

pub fn join(coins: &[K], rest: &[K], c: &mut [K]) {
    assert!(coins.len() >= COINS && rest.len() >= REST && c.len() >= N);
    let mut at = 0;
    for j in 0..1023 {
        let selected = j >= 128 && j <= 938 && (j - 128) % 3 == 0;
        if selected {
            c[j] = coins[(j - 128) / 3];
        } else {
            c[j] = rest[at];
            at += 1;
        }
    }
    c[1023] = K::ZERO;
}

/// Sparse terminal in code coordinates. `sums` is caller-owned interleaved
/// `(normal,carry)` storage for all 64 groups; index 64 is zero-extended.
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
    for i in 0..COINS {
        let row = slot(i);
        let group = row >> 4;
        let low = row & 15;
        sums[2 * group] = sums[2 * group].add(coins[i].mul(normal[low]));
        if low < 3 {
            sums[2 * group + 1] = sums[2 * group + 1].add(coins[i].mul(carry[low]));
        }
    }
    let mut out = [K::ZERO; 4];
    for group in 0..4 {
        let mut left = [K::ZERO; 4];
        let mut right = [K::ZERO; 4];
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
            value = value.add(sums[2 * j]);
            let lane4 = lane & 3;
            left[lane4] = high[lane];
            right[lane4] = value;
            if lane4 == 3 {
                out[group] = out[group].add(qm31_sum_products4(left, right));
            }
        }
    }
    for value in &mut out {
        for _ in 0..8 {
            *value = value.half();
        }
    }
    out
}
