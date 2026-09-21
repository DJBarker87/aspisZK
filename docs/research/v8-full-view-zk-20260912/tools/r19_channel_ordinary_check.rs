//! Arbitrary-input source differential for the R19 channel ordinary terminal.
//!
//! This is a finite-field equality checker only.  It makes no cryptographic,
//! probability, or protocol-closure claim.
extern crate aspis_core as corelib;

#[path="r16_basis_transport.rs"] mod basis_transport;
mod r17_tensor_prefix;
mod r17_owned_weights;
mod r17_structured_g;
use r17_structured_g as structured_g;
mod r18_sparse_coded_g;
mod r18_compact_g;
mod r17_mask_workspace;
mod r17_opening_weights;
mod r17_weighted_groups;
mod r19_channel_ordinary;

use corelib::field::{CM31, M31, QM31 as K, P};
use corelib::sumcheck::WeightAccumulator;

fn sample(n: u32) -> K {
    K { c0: CM31::new(M31(n % P), M31((n.wrapping_mul(3) + 7) % P)),
        c1: CM31::new(M31((n.wrapping_mul(5) + 11) % P), M31((n.wrapping_mul(7) + 13) % P)) }
}

fn fold(v: Vec<K>, alpha: [K; 4]) -> [K; 4] {
    let mut w = WeightAccumulator::empty(10);
    w.add_dense(v).unwrap();
    for a in alpha { w.fold_deferred_relation_arity4(a); }
    w.weight_prefix::<4>()
}

fn dot(a: [K; 4], b: [K; 4]) -> K { corelib::field::qm31_sum_products4(a, b) }

fn image_weights(linear: K, quadratic: K, b: K, c: K) -> Vec<K> {
    let mut w = vec![K::ZERO; 1024];
    w[1023] = linear;
    w[1022] = quadratic.mul(b);
    w[1021] = quadratic.mul(c).neg();
    w
}

fn image_terminal(t: K, b: K, c: K, a: [K; 4]) -> K {
    let a0 = a[0];
    let inner = t.mul(a0).add(t.square().mul(b.mul(a0.square())
        .sub(c.mul(a0.square().mul(a0)))));
    a[1].mul(a[2]).mul(a[3]).mul(inner).mul_m31(M31(8_388_608))
}

fn main() {
    let transport = basis_transport::transport();
    let mut channel_cases = 0usize;
    let mut image_cases = 0usize;
    for case in 0..48u32 {
        let z = core::array::from_fn(|i| if case == 0 { K::ZERO }
            else if case == 1 { K::ONE } else { sample(case * 37 + i as u32) });
        let kappa = sample(101 + case * 5);
        let audit = core::array::from_fn(|i| if i < 10 { z[i] } else { kappa });
        let abc = core::array::from_fn(|i| sample(401 + case * 3 + i as u32));
        let alpha = if case == 3 { [K::ZERO; 4] } else if case == 4 {
            [K::ONE; 4]
        } else { core::array::from_fn(|i| sample(801 + case * 4 + i as u32)) };
        let beta = match case {
            0 => K::ZERO,
            1 => K::ONE,
            2 => K::ONE.neg(),
            _ => sample(1201 + case),
        };
        let mut workspace = vec![K::ZERO; 1024];
        let ordinary = r19_channel_ordinary::terminal(&audit, abc, alpha, beta, &mut workspace);
        let compact = r18_compact_g::terminal(&z, abc, alpha, &mut workspace);
        let candidate = core::array::from_fn(|i| ordinary[i].add(beta.mul(kappa).mul(compact[i])));

        let r = r17_opening_weights::chord_transpose(&transport.dual(
            &r17_opening_weights::original_weights_reference(&z, kappa, false)), abc);
        let g = r17_opening_weights::chord_transpose(&transport.dual(
            &r17_opening_weights::original_weights_reference(&z, kappa, true)), abc);
        let dense = fold((0..1024).map(|i| r[i].add(beta.mul(g[i].sub(r[i])))).collect(), alpha);
        assert_eq!(candidate, dense, "ordinary/G dense lerp case {case}");
        channel_cases += 1;

        let tau = match case {
            5 => K::ZERO,
            6 => K::ONE,
            7 => K::ONE.neg(),
            _ => sample(1601 + case),
        };
        let b = sample(1701 + case);
        let c = sample(1801 + case);
        let finals = core::array::from_fn(|i| sample(1901 + case * 4 + i as u32));
        let ir = image_weights(tau, tau.square(), b, c);
        let ig = image_weights(tau.pow(3), tau.pow(4), b, c);
        let mixed = (0..1024).map(|i| ir[i].add(beta.mul(ig[i].sub(ir[i])))).collect();
        let dense_image = dot(fold(mixed, alpha), finals);
        let image_scale = K::ONE.sub(beta).add(beta.mul(tau.square()));
        let source_image = image_scale.mul(image_terminal(tau, b, c, alpha)).mul(finals[3]);
        assert_eq!(dense_image, source_image, "mixed image weights case {case}");
        image_cases += 1;
    }
    println!("{{\"channel_terminal_cases\":{channel_cases},\"mixed_image_cases\":{image_cases},\"betas\":[\"0\",\"1\",\"-1\",\"random\"],\"all_passed\":true,\"source_validated\":true,\"privacy_or_soundness_claim\":false}}");
}
