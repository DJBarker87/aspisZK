//! RESEARCH CANDIDATE, NOT A PRODUCTION PATCH.
//! Replace Vandermonde mixing by spaced coordinates of c = T(g).
//! Must be used under a NEW profile and source/full-view gates in CODEX_TASK.md.
//! This file was not compiled in the review environment.
use aspis_core::field::{M31, M31_HALF, QM31 as K};

pub const N: usize = 1024;
pub const COINS: usize = 271;
pub const REST: usize = 752;
pub const fn slot(i: usize) -> usize { 128 + 3 * i }

/// Source T has c[j] = g[order[j]] for j != 1023.
/// The order is immutable verifier-derived data, NOT a prover supplied map.
pub fn mixed_coins(g: &[K; N], order: &[usize; N]) -> [K; COINS] {
    core::array::from_fn(|i| g[order[slot(i)]])
}

/// Same structured ten-round mask coefficients as R17; different placement.
/// Its arithmetic is deliberately explicit for comparison with the retained source.
pub fn coin_weights(point: &[K; 10], out: &mut [K; COINS]) {
    let mut scale = K::ONE;
    for r in (0..10).rev() {
        let start = 1 + 27 * r;
        let x = point[r];
        out[start] = scale.mul(K::ONE.sub(x.add(x)));
        let mut power = x.square();
        for i in 1..27 {
            out[start + i] = scale.mul(power.sub(x));
            power = power.mul(x);
        }
        scale = scale.mul_m31(M31_HALF);
    }
    out[0] = scale;
}

/// Prover/reference route: the original-row functional scatters to order[S].
/// This helper is not intended to materialize a dense vector in the SBF verifier.
pub fn original_weights_into(
    point: &[K; 10], order: &[usize; N], coins: &mut [K; COINS], out: &mut [K; N],
) {
    coin_weights(point, coins);
    out.fill(K::ZERO);
    for i in 0..COINS { out[order[slot(i)]] = coins[i]; }
}

/// Exact full coin codec on the legal balanced coefficient space c[1023]=0.
/// Rest coordinates are retained in increasing coefficient order.
pub fn split(c: &[K; N], coins: &mut [K; COINS], rest: &mut [K; REST]) -> bool {
    if c[1023] != K::ZERO { return false; }
    for i in 0..COINS { coins[i] = c[slot(i)]; }
    let mut at = 0;
    for j in 0..1023 {
        let selected = j >= 128 && j <= 938 && (j - 128) % 3 == 0;
        if !selected { rest[at] = c[j]; at += 1; }
    }
    at == REST
}
pub fn join(coins: &[K; COINS], rest: &[K; REST], c: &mut [K; N]) {
    let mut at = 0;
    for j in 0..1023 {
        let selected = j >= 128 && j <= 938 && (j - 128) % 3 == 0;
        if selected { c[j] = coins[(j - 128) / 3]; }
        else { c[j] = rest[at]; at += 1; }
    }
    c[1023] = K::ZERO;
}

/// Reuses the retained grouped natural-chord geometry, without T corrections:
/// these weights ALREADY live in code coefficient coordinates.
/// Supply the same normal/carry/high arrays computed by R17 Kernel::new.
/// Caller supplies reusable 64-pair scratch; no heap allocation is performed.
/// Keep ALL 64 high groups, including carries from nonzero input groups.
pub fn sparse_terminal(
    coins: &[K; COINS], normal: &[K; 16], carry: &[K; 3], high: &[K; 16],
    sums: &mut [(K, K); 64],
) -> [K; 4] {
    sums.fill((K::ZERO, K::ZERO));
    for i in 0..COINS {
        let row = slot(i);
        let group = row >> 4;
        let low = row & 15;
        sums[group].0 = sums[group].0.add(coins[i].mul(normal[low]));
        if low < 3 { sums[group].1 = sums[group].1.add(coins[i].mul(carry[low])); }
    }
    let mut out = [K::ZERO; 4];
    for j in 0usize..64 {
        // Nested-halving form of the source carry; final index 64 is zero.
        let mut bits = j.trailing_ones() as usize;
        let mut value = if j + 1 < 64 { sums[j + 1].1 } else { K::ZERO };
        while bits != 0 {
            bits -= 1;
            let row = j & !((1usize << (bits + 1)) - 1);
            value = value.add(sums[row].1).half();
        }
        value = value.add(sums[j].0);
        out[j >> 4] = out[j >> 4].add(value.mul(high[j & 15]));
    }
    for value in &mut out { for _ in 0..8 { *value = value.half(); } }
    out
}

// Deliberately no deployment, parser bypass, challenge change, or automatic source edit.
// The original M31 type is referenced explicitly for downstream fixed constant checks.
const _: M31 = M31_HALF;
