//! Focused same-profile R19 control.
//!
//! Every oracle state below is the production `WeightAccumulator`; the test
//! does not implement an independent weight model.  It compares the adapter's
//! one R-channel state against the two old channel states at injection and
//! after each of the three unchanged relation folds, then checks the terminal
//! pairing with arbitrary full-QM31 final vectors.
extern crate aspis_core as corelib;

use corelib::field::{qm31_sum_products4, CM31, M31, QM31 as K, P};
use corelib::sumcheck::WeightAccumulator;

#[path = "r19_shared_queries.rs"]
mod shared_queries;

const Q: usize = 22;

fn sample_m31(state: &mut u64) -> M31 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    M31((*state % u64::from(P)) as u32)
}

fn sample_k(state: &mut u64) -> K {
    K { c0: CM31::new(sample_m31(state), sample_m31(state)),
        c1: CM31::new(sample_m31(state), sample_m31(state)) }
}

fn scales(rho: K) -> [K; Q] {
    let mut out = [K::ZERO; Q];
    let mut power = rho;
    for item in &mut out {
        *item = power;
        power = power.mul(rho);
    }
    out
}

fn assert_weights(shared: &WeightAccumulator, old_r: &WeightAccumulator,
                 old_g: &WeightAccumulator, lambda: K, len: usize) {
    for i in 0..len {
        let r = old_r.weight_at(i as u32);
        assert_eq!(shared.weight_at(i as u32), r, "R state at {i}");
        assert_eq!(old_g.weight_at(i as u32), lambda.mul(r), "G state at {i}");
    }
}

fn main() {
    let mut state = 0x5241_9736_8617_7265u64;
    for case in 0..64 {
        let mut rho = sample_k(&mut state);
        if case == 0 { rho = K::ZERO; }
        if case == 1 { rho = K::ONE; }
        if case == 2 { rho = K::ONE.neg(); }
        let xs: [M31; Q] = core::array::from_fn(|_| sample_m31(&mut state));
        let r: [K; Q] = core::array::from_fn(|_| sample_k(&mut state));
        let g: [K; Q] = core::array::from_fn(|_| sample_k(&mut state));
        let s = scales(rho);
        let lambda = s[21];

        let mut old_r = WeightAccumulator::empty(8);
        let mut old_g = WeightAccumulator::empty(8);
        old_r.add_line_m31_batch(&s, &xs).unwrap();
        let gs = s.map(|x| lambda.mul(x));
        old_g.add_line_m31_batch(&gs, &xs).unwrap();
        let mut shared = shared_queries::prepare(&xs, &r, &g, rho).unwrap();
        assert_eq!(shared.lambda, lambda);

        // This is the exact old 44-power increment, retained as the byte-level
        // transcript oracle; the adapter's formula must serialize identically.
        let mut power = rho;
        let mut old_increment = K::ZERO;
        for value in r.iter().chain(g.iter()) {
            old_increment = old_increment.add(power.mul(*value));
            power = power.mul(rho);
        }
        assert_eq!(shared.increment, old_increment);
        assert_weights(&shared.weights, &old_r, &old_g, lambda, 256);

        for fold in 0..3 {
            let alpha = sample_k(&mut state);
            shared.fold(alpha);
            old_r.fold_deferred_relation_arity4(alpha);
            old_g.fold_deferred_relation_arity4(alpha);
            assert_weights(&shared.weights, &old_r, &old_g, lambda,
                           256 >> (2 * (fold + 1)));
        }

        let final_r = core::array::from_fn(|_| sample_k(&mut state));
        let final_g = core::array::from_fn(|_| sample_k(&mut state));
        let combined = shared.final_values(final_r, final_g);
        let r_terminal = old_r.weight_prefix::<4>();
        let g_terminal = old_g.weight_prefix::<4>();
        let lhs = qm31_sum_products4(r_terminal, final_r)
            .add(qm31_sum_products4(g_terminal, final_g));
        let rhs = qm31_sum_products4(r_terminal, combined);
        assert_eq!(lhs, rhs, "terminal pairing case {case}");
    }
    // Shape/error mapping remains the old Option contract.
    let z = [M31::ZERO; Q];
    let k = [K::ZERO; Q];
    assert!(shared_queries::prepare(&z[..21], &k, &k, K::ZERO).is_none());
    assert!(shared_queries::prepare(&z, &k[..21], &k, K::ZERO).is_none());
    assert!(shared_queries::prepare(&z, &k, &k[..21], K::ZERO).is_none());
    println!("PASS R19 shared query accumulator: 64 arbitrary full-QM31 cases; rho=0,1,-1; insertion + 3 folds + terminal pairing; malformed lengths preserved");
}
