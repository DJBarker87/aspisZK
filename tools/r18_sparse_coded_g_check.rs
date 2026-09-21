//! Differential controls for R18 sparse code-coordinate G.
//! The retained actual chord and WeightAccumulator/four-fold path is used as
//! the independent reference; this remains tooling, not production code.
extern crate aspis_core as corelib;
mod sparse_coded_g {
    include!("r18_sparse_coded_g.rs");
}
use corelib::field::{CM31, M31, M31_HALF, P, QM31 as K};
use corelib::sumcheck::WeightAccumulator;
// The stager places this checker beside the retained grouped implementation;
// keep the path relative so the staged source remains portable.
#[path = "r17_weighted_groups.rs"]
mod retained_grouped;
#[path = "r16_basis_transport.rs"]
mod basis_transport;
use sparse_coded_g::*;

fn sample(n: u32) -> K {
    K {
        c0: CM31::new(M31(n % P), M31((n * 3 + 7) % P)),
        c1: CM31::new(M31((n * 5 + 11) % P), M31((n * 7 + 13) % P)),
    }
}

fn edges(mut row: usize) -> Vec<(usize, M31)> {
    let mut bit = 0;
    let mut scale = M31::ONE;
    let mut out = Vec::new();
    while row & (1 << bit) != 0 {
        row ^= 1 << bit;
        scale = scale.mul(M31_HALF);
        out.push((row, scale));
        bit += 1;
    }
    out.push((row | (1 << bit), scale));
    out
}

// Retained source chord-transpose reference, including its 513/512/512
// intermediate shape; this is intentionally independent of sparse_terminal.
fn chord_transpose(w: &[K], [a, b, c]: [K; 3]) -> Vec<K> {
    let mut w = w.to_vec();
    w.resize(1028, K::ZERO);
    let even: Vec<_> = w.chunks_exact(2).map(|v| v[0]).collect();
    let odd: Vec<_> = w.chunks_exact(2).map(|v| v[1]).collect();
    let xt = |v: &[K], n: usize| {
        (0..n)
            .map(|j| {
                let (mut row, mut bit, mut scale, mut sum) = (j, 0, M31::ONE, K::ZERO);
                while row & (1 << bit) != 0 {
                    row ^= 1 << bit;
                    scale = scale.mul(M31_HALF);
                    sum = sum.add(v[row].mul_m31(scale));
                    bit += 1;
                }
                sum.add(v[row | (1 << bit)].mul_m31(scale))
            })
            .collect::<Vec<_>>()
    };
    let x_even = xt(&even, 513);
    let xx_even = xt(&x_even, 512);
    let x_odd = xt(&odd, 512);
    let mut out = vec![K::ZERO; N];
    for j in 0..512 {
        out[2 * j] = a.mul(even[j]).add(b.mul(x_even[j])).add(c.mul(odd[j]));
        out[2 * j + 1] = c
            .mul(even[j].sub(xx_even[j]))
            .add(a.mul(odd[j]))
            .add(b.mul(x_odd[j]));
    }
    out
}

fn basis(a: K, b: K) -> [K; 16] {
    let a2 = a.square();
    let b2 = b.square();
    let ap = [K::ONE, a2.mul(a), a2, a];
    let bp = [K::ONE, b2.mul(b), b2, b];
    core::array::from_fn(|j| {
        if j < 4 {
            ap[j]
        } else if j % 4 == 0 {
            bp[j / 4]
        } else {
            ap[j % 4].mul(bp[j / 4])
        }
    })
}

fn geometry([a, b, c]: [K; 3], alpha: [K; 4]) -> ([K; 16], [K; 3], [K; 16]) {
    let low = basis(alpha[0], alpha[1]);
    let high = basis(alpha[2], alpha[3]);
    let mut xn = [K::ZERO; 16];
    let mut xc = [K::ZERO; 16];
    let mut yn = [K::ZERO; 16];
    let mut yc = [K::ZERO; 16];
    for input in 0..16 {
        let y = input & 1;
        let j = input >> 1;
        for (r, s) in edges(j) {
            let dest = 2 * (r % 8) + y;
            if r < 8 {
                xn[dest] = xn[dest].add(low[input].mul_m31(s));
            } else {
                xc[dest] = xc[dest].add(low[input].mul_m31(s));
            }
        }
        if y == 0 {
            yn[input + 1] = yn[input + 1].add(low[input]);
        } else {
            yn[input - 1] = yn[input - 1].add(low[input].half());
            for (r, s) in edges(j >> 1) {
                let line = (r << 1) | (j & 1);
                let dest = 2 * (line % 8);
                let v = low[input].mul_m31(s).half();
                if line < 8 {
                    yn[dest] = yn[dest].sub(v);
                } else {
                    yc[dest] = yc[dest].sub(v);
                }
            }
        }
    }
    let normal = core::array::from_fn(|j| a.mul(low[j]).add(b.mul(xn[j])).add(c.mul(yn[j])));
    let carry = [b.mul(xc[0]).add(c.mul(yc[0])), b.mul(xc[1]), c.mul(yc[2])];
    (normal, carry, high)
}

fn direct_fourfold(c: &[K], abc: [K; 3], alpha: [K; 4]) -> [K; 4] {
    let chord = chord_transpose(c, abc);
    let mut w = WeightAccumulator::empty(10);
    w.add_dense(chord).unwrap();
    for a in alpha {
        w.fold_deferred_relation_arity4(a);
    }
    w.weight_prefix::<4>()
}

fn main() {
    let map=basis_transport::transport();
    let order: &[usize;N]=map.order.as_slice().try_into().unwrap();
    for case in 0..32u32 {
        let c: Vec<_> = (0..1023)
            .map(|j| sample(case * 1024 + j))
            .chain([K::ZERO])
            .collect();
        let mut coins = vec![K::ZERO; COINS];
        let mut rest = vec![K::ZERO; REST];
        assert!(split(&c, &mut coins, &mut rest));
        let mut joined = vec![K::ZERO; N];
        join(&coins, &rest, &mut joined);
        assert_eq!(joined, c);
        let original_g=map.inverse(&c);
        assert_eq!(map.forward(&original_g),c);
        let mut recovered_coins=vec![K::ZERO;COINS];
        let mut recovered_rest=vec![K::ZERO;REST];
        assert!(split(&joined,&mut recovered_coins,&mut recovered_rest));
        assert_eq!(recovered_coins,coins);assert_eq!(recovered_rest,rest);
        let mut invalid=c.clone();invalid[1023]=K::ONE;
        assert!(!split(&invalid,&mut recovered_coins,&mut recovered_rest));
        // Preserve the split coordinates before the weight helpers reuse the
        // caller-owned coin buffer for their output coefficients.
        let arbitrary_coins = coins.clone();
        let mut mixed = vec![K::ZERO; COINS];
        mixed_coins_into(&original_g, order, &mut mixed);
        assert_eq!(mixed, coins);
        let mut coin_weights_buf = vec![K::ZERO; COINS];
        coin_weights_into(&c[..10], &mut coin_weights_buf);
        let mut original = vec![K::ZERO; N];
        original_weights_into(&c[..10], order, &mut coins, &mut original);
        let mut code = vec![K::ZERO; N];
        code_weights_into(&c[..10], &mut coins, &mut code);
        assert_eq!(map.dual(&original),code,"source sparse transport cancellation");
        let dot=|a:&[K],b:&[K]|a.iter().zip(b).fold(K::ZERO,|s,(&a,&b)|s.add(a.mul(b)));
        assert_eq!(dot(&original,&original_g),dot(&code,&c));
        for i in 0..COINS {
            assert_eq!(original[order[slot(i)]], code[slot(i)]);
        }
        let abc = if case == 0 {
            [K::ZERO; 3]
        } else {
            [sample(case + 3), sample(case + 7), sample(case + 11)]
        };
        let alpha = if case == 1 {
            [K::ONE; 4]
        } else {
            [
                sample(case + 21),
                sample(case + 27),
                sample(case + 33),
                sample(case + 39),
            ]
        };
        let (normal, carry, high) = geometry(abc, alpha);
        let retained = retained_grouped::Kernel::new(abc, alpha);
        for basis_coin in 0..COINS {
            let mut one = vec![K::ZERO; COINS];
            one[basis_coin] = K::ONE;
            let mut code = vec![K::ZERO; N];
            let empty = vec![K::ZERO; REST];
            join(&one, &empty, &mut code);
            let mut sums = vec![K::ZERO; 128];
            assert_eq!(
                sparse_terminal(&one, &normal, &carry, &high, &mut sums),
                retained.prefix(&code)
            );
            assert_eq!(
                sparse_terminal(&one, &normal, &carry, &high, &mut sums),
                direct_fourfold(&code, abc, alpha)
            );
        }
        let mut sums = vec![K::ZERO; 128];
        let mut arbitrary_code = vec![K::ZERO; N];
        let empty = vec![K::ZERO; REST];
        join(&arbitrary_coins, &empty, &mut arbitrary_code);
        assert_eq!(
            sparse_terminal(&arbitrary_coins, &normal, &carry, &high, &mut sums),
            retained.prefix(&arbitrary_code)
        );
        assert_eq!(
            sparse_terminal(&arbitrary_coins, &normal, &carry, &high, &mut sums),
            direct_fourfold(&arbitrary_code, abc, alpha)
        );
    }
    println!("PASS: 32 split/join, code/original scatter, mixed-coin, and bounded sparse-terminal controls");
    println!("BOUNDARY: retained chord/four-fold geometry differential only; no protocol or security claim");
}
