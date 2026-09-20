//! Proposed structured mask. Research/test module only; not a source profile.
use aspis_core::field::{CM31, M31, M31_HALF, QM31 as K};

pub(super) const N: usize = 1024;
pub(super) const ROUNDS: usize = 10;
pub(super) const PER_ROUND: usize = 27;
pub(super) const COINS: usize = 1 + ROUNDS * PER_ROUND;

fn scalar(i: usize) -> K {
    K::from_cm31(CM31::from_m31(M31(i as u32)))
}

pub(super) fn mixing_row(i: usize) -> Vec<K> {
    assert!(i < N);
    let node = scalar(i + 1);
    let mut power = K::ONE;
    (0..N)
        .map(|_| {
            let out = power;
            power = power.mul(node);
            out
        })
        .collect()
}

pub(super) fn mixed_coins(g: &[K]) -> [K; COINS] {
    assert_eq!(g.len(), N);
    core::array::from_fn(|i| {
        let node = scalar(i + 1);
        g.iter().rev().fold(K::ZERO, |v, &c| v.mul(node).add(c))
    })
}

fn zero_boundary(u: &[K], x: K) -> K {
    assert_eq!(u.len(), PER_ROUND);
    let mut out = u[0].mul(K::ONE.sub(x.add(x)));
    let mut power = x.square();
    for &c in &u[1..] {
        out = out.add(c.mul(power.sub(x)));
        power = power.mul(x);
    }
    out
}

pub(super) fn mask_eval(coins: &[K; COINS], point: &[K; ROUNDS]) -> K {
    let half = K::from_cm31(CM31::from_m31(M31_HALF));
    let mut scale = K::ONE;
    let mut out = K::ZERO;
    for r in (0..ROUNDS).rev() {
        let start = 1 + r * PER_ROUND;
        out = out.add(zero_boundary(&coins[start..start + PER_ROUND], point[r]).mul(scale));
        scale = scale.mul(half);
    }
    out.add(coins[0].mul(scale))
}

pub(super) fn round_coefficients(carry: K, u: &[K]) -> [K; 28] {
    assert_eq!(u.len(), PER_ROUND);
    let mut out = [K::ZERO; 28];
    out[0] = carry.mul_m31(M31_HALF).add(u[0]);
    out[1] = u[0].add(u[0]).neg();
    for (i, &v) in u[1..].iter().enumerate() {
        out[i + 2] = v;
        out[1] = out[1].sub(v);
    }
    out
}

pub(super) fn mask_weights(point: &[K; ROUNDS]) -> Vec<K> {
    let mut coin_weights = [K::ZERO; COINS];
    let mut scale = K::ONE;
    for r in (0..ROUNDS).rev() {
        let start = 1 + r * PER_ROUND;
        let x = point[r];
        coin_weights[start] = scale.mul(K::ONE.sub(x.add(x)));
        let mut power = x.square();
        for i in 1..PER_ROUND {
            coin_weights[start + i] = scale.mul(power.sub(x));
            power = power.mul(x);
        }
        scale = scale.mul_m31(M31_HALF);
    }
    coin_weights[0] = scale;
    let mut weights = vec![K::ZERO; N];
    for (i, &a) in coin_weights.iter().enumerate() {
        for (w, b) in weights.iter_mut().zip(mixing_row(i)) {
            *w = w.add(a.mul(b));
        }
    }
    weights
}

#[test]
fn r17_structured_g_round_algebra_and_functional() {
    fn sample(i: usize) -> K {
        let i = i as u32;
        K {
            c0: CM31::new(M31(i + 1), M31(3 * i + 7)),
            c1: CM31::new(M31(5 * i + 11), M31(7 * i + 13)),
        }
    }
    let g: Vec<_> = (0..N).map(sample).collect();
    let coins = mixed_coins(&g);
    for (i, &coin) in coins.iter().enumerate() {
        assert_eq!(
            coin,
            g.iter()
                .zip(mixing_row(i))
                .fold(K::ZERO, |v, (&a, b)| v.add(a.mul(b)))
        );
    }
    let z: [K; ROUNDS] = core::array::from_fn(|i| sample(1200 + i));
    let initial = (0..N).fold(K::ZERO, |sum, row| {
        let p = core::array::from_fn(|bit| scalar((row >> (9 - bit)) & 1));
        sum.add(mask_eval(&coins, &p))
    });
    assert_eq!(initial, coins[0]);
    let mut carry = initial;
    for round in 0..ROUNDS {
        let start = 1 + round * PER_ROUND;
        let u = &coins[start..start + PER_ROUND];
        let coeff = round_coefficients(carry, u);
        let eval = |x| coeff.iter().rev().fold(K::ZERO, |v, &a| v.mul(x).add(a));
        assert_eq!(eval(K::ZERO).add(eval(K::ONE)), carry);
        // The source sends c0,c2,...,c27. Their inverse recovers exactly u.
        assert_eq!(coeff[0].sub(carry.mul_m31(M31_HALF)), u[0]);
        assert_eq!(&coeff[2..], &u[1..]);
        for x in (0..28).map(scalar).chain(core::iter::once(z[round])) {
            let suffix_bits = ROUNDS - 1 - round;
            let direct = (0..1 << suffix_bits).fold(K::ZERO, |sum, suffix| {
                let mut p = z;
                p[round] = x;
                for b in 0..suffix_bits {
                    p[round + 1 + b] = scalar((suffix >> (suffix_bits - 1 - b)) & 1);
                }
                sum.add(mask_eval(&coins, &p))
            });
            assert_eq!(direct, eval(x), "round={round}");
        }
        carry = eval(z[round]);
    }
    let terminal = mask_eval(&coins, &z);
    assert_eq!(carry, terminal);
    assert_eq!(
        terminal,
        g.iter()
            .zip(mask_weights(&z))
            .fold(K::ZERO, |v, (&a, b)| v.add(a.mul(b)))
    );
    println!("R17_STRUCTURED_G coins=271 rounds=10 suffix_checks=290 boundary_checks=10 terminal_functional=true");
}

#[test]
fn r17_structured_g_unchanged_shared_functional_negative() {
    use aspis_core::sumcheck::WeightAccumulator;
    let z = core::array::from_fn(|i| scalar(i + 2));
    let wg = mask_weights(&z);
    let mut ordinary = WeightAccumulator::empty(10);
    ordinary.add_multilinear(K::ONE, z.to_vec()).unwrap();
    let inactive = &super::basis_transport::transport().inactive;
    let anchor = (0..N).find(|&i| inactive[i]).unwrap();
    let difference = |i: usize| wg[i].sub(ordinary.weight_at(i as u32));
    let row = (0..N)
        .find(|&i| inactive[i] && difference(i) != difference(anchor))
        .unwrap();
    let gamma = scalar(7);
    // Algebraic collision in the single batched message, not a forged source
    // proof: H1 changes by -gamma*d and G by d. Both are QM31 columns.
    let mut dh = vec![K::ZERO; N];
    let mut dg = vec![K::ZERO; N];
    dh[row] = gamma.neg();
    dh[anchor] = gamma;
    dg[row] = K::ONE;
    dg[anchor] = K::ONE.neg();
    let mut h1 = vec![K::ZERO; N];
    crate::state_only_hiding::apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h1, &dh).unwrap();
    assert_eq!(h1, dh);
    let gh = gamma.pow(26);
    let gg = gamma.pow(27);
    assert!((0..N).all(|i| gh.mul(dh[i]).add(gg.mul(dg[i])) == K::ZERO));
    let ordinary_delta = ordinary
        .weight_at(row as u32)
        .sub(ordinary.weight_at(anchor as u32));
    let proposed_claim_change = gh
        .mul(gamma.neg().mul(ordinary_delta))
        .add(gg.mul(wg[row].sub(wg[anchor])));
    assert_ne!(proposed_claim_change, K::ZERO);
    // A new common functional cannot fix this: every linear functional of
    // the zero combined message is zero, while the required claim is not.
    println!("R17_SHARED_FUNCTIONAL_NEGATIVE rows={anchor},{row} legal_h1_pad=true combined_delta=0 required_claim_delta_nonzero=true");
}
