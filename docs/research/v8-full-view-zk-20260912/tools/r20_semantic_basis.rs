//! Source-local semantic basis candidate for the actual QM31 representation.
//!
//! The caller owns `basis`/`coins` storage and supplies the source-local
//! whole-dot function.  No cache hint is accepted: every basis entry is
//! recomputed from that round's actual challenge.
use aspis_core::field::{M31, M31_HALF, P, QM31 as K};

pub const ROUNDS: usize = 10;
pub const ROUND_TERMS: usize = 27;
pub const TOTAL_BASIS: usize = ROUNDS * ROUND_TERMS;
pub const COINS: usize = 271;

#[inline(never)]
pub fn basis_into(x: K, out: &mut [K; ROUND_TERMS]) {
    out[0] = K::ONE.sub(x.add(x));
    let mut power = x.square();
    for i in 1..ROUND_TERMS {
        out[i] = power.sub(x);
        if i + 1 < ROUND_TERMS {
            power = power.mul(x);
        }
    }
}

/// Evaluate claim*x + sum(sent[i] * basis[i]) using the caller's whole-dot
/// candidate.  The source adapter must validate canonical sent/challenge
/// representations at its real boundary before invoking the dot contract.
#[inline(never)]
pub fn evaluate_round_with_dot(
    claim: K,
    sent: &[K; ROUND_TERMS],
    x: K,
    basis: &mut [K; ROUND_TERMS],
    whole_dot: fn(&[K], &[K]) -> K,
) -> K {
    basis_into(x, basis);
    claim.mul(x).add(whole_dot(sent, basis))
}

/// Direct source-local entrypoint when the sibling whole-dot module is named
/// `r20_whole_dot`.  This module is not a public field API.
#[inline(never)]
pub fn evaluate_round(claim: K, sent: &[K; ROUND_TERMS], x: K, basis: &mut [K; ROUND_TERMS]) -> K {
    evaluate_round_with_dot(claim, sent, x, basis, |a, b| {
        crate::r20_whole_dot::dot(a, b).expect("canonical source dot contract")
    })
}

/// Scale a caller-owned 10-round basis cache into the 271 coin layout used by
/// the existing source.  The chronology is exactly the baseline: round 9 is
/// scaled by one, then each preceding round by one further M31 half; coin 0
/// is one scaled by 1/1024.
#[inline(never)]
pub fn scale_round_basis_into(basis: &[K; TOTAL_BASIS], coins: &mut [K; COINS]) {
    let mut scale = M31::ONE;
    for r in (0..ROUNDS).rev() {
        let start = ROUND_TERMS * r;
        let dst = 1 + start;
        for i in 0..ROUND_TERMS {
            coins[dst + i] = basis[start + i].mul_m31(scale);
        }
        scale = scale.mul(M31_HALF);
    }
    coins[0] = K::ONE.mul_m31(scale);
}

#[inline(always)]
fn horner_round(claim: K, sent: &[K; ROUND_TERMS], x: K) -> K {
    let mut coeff = [K::ZERO; 28];
    coeff[0] = sent[0];
    coeff[1] = claim.sub(sent[0].add(sent[0]));
    for i in 1..ROUND_TERMS {
        coeff[1] = coeff[1].sub(sent[i]);
        coeff[i + 1] = sent[i];
    }
    let mut out = coeff[27];
    for i in (0..27).rev() {
        out = out.mul(x).add(coeff[i]);
    }
    out
}

#[inline(always)]
fn sample(n: u32) -> K {
    let q = |v: u32| M31(v % P);
    K {
        c0: aspis_core::field::CM31::new(q(n), q(n.wrapping_mul(3).wrapping_add(7))),
        c1: aspis_core::field::CM31::new(
            q(n.wrapping_mul(5).wrapping_add(11)),
            q(n.wrapping_mul(7).wrapping_add(13)),
        ),
    }
}

fn all_max() -> K {
    let p = M31(P - 1);
    K {
        c0: aspis_core::field::CM31::new(p, p),
        c1: aspis_core::field::CM31::new(p, p),
    }
}

/// Independent host differential for the parent harness.  It checks 2560
/// round evaluations against reconstructed 28-coefficient Horner, then checks
/// all ten scaled basis blocks against the retained coin-weight chronology.
/// The final two assertions deliberately mutate/reorder a cache and must fail
/// equality, proving the checker would detect stale or reordered cache data.
pub fn differential_check(whole_dot: fn(&[K], &[K]) -> K) {
    let mut basis = [K::ZERO; ROUND_TERMS];
    for case in 0..2560u32 {
        let mut sent = [K::ZERO; ROUND_TERMS];
        for i in 0..ROUND_TERMS {
            sent[i] = if case % 31 == 0 {
                all_max()
            } else {
                sample(case.wrapping_mul(29).wrapping_add(i as u32 + 1))
            };
        }
        let x = match case % 5 {
            0 => K::ZERO,
            1 => K::ONE,
            2 => all_max(),
            _ => sample(case.wrapping_mul(17).wrapping_add(901)),
        };
        let claim = sample(case.wrapping_mul(43).wrapping_add(1901));
        let got = evaluate_round_with_dot(claim, &sent, x, &mut basis, whole_dot);
        assert_eq!(got, horner_round(claim, &sent, x), "semantic round {case}");
    }

    let points: [K; ROUNDS] = core::array::from_fn(|r| sample(50_001 + r as u32 * 97));
    let mut all_basis = [K::ZERO; TOTAL_BASIS];
    let mut expected = [K::ZERO; COINS];
    let mut one = [K::ZERO; ROUND_TERMS];
    for r in 0..ROUNDS {
        basis_into(points[r], &mut one);
        all_basis[r * ROUND_TERMS..(r + 1) * ROUND_TERMS].copy_from_slice(&one);
        expected[1 + r * ROUND_TERMS] = K::ONE.sub(points[r].add(points[r]));
        let mut power = points[r].square();
        for i in 1..ROUND_TERMS {
            expected[1 + r * ROUND_TERMS + i] = power.sub(points[r]);
            if i + 1 < ROUND_TERMS {
                power = power.mul(points[r]);
            }
        }
    }
    let mut scale = M31::ONE;
    for r in (0..ROUNDS).rev() {
        for i in 0..ROUND_TERMS {
            expected[1 + r * ROUND_TERMS + i] = expected[1 + r * ROUND_TERMS + i].mul_m31(scale);
        }
        scale = scale.mul(M31_HALF);
    }
    expected[0] = K::ONE.mul_m31(scale);
    let mut coins = [K::ZERO; COINS];
    scale_round_basis_into(&all_basis, &mut coins);
    assert_eq!(coins, expected, "ten-round scaled coin cache");

    let mut stale = all_basis;
    stale[0] = stale[0].add(K::ONE);
    let mut stale_coins = [K::ZERO; COINS];
    scale_round_basis_into(&stale, &mut stale_coins);
    assert_ne!(stale_coins, coins, "stale cache must be detected");
    let mut reordered = all_basis;
    reordered.swap(0, ROUND_TERMS);
    let mut reordered_coins = [K::ZERO; COINS];
    scale_round_basis_into(&reordered, &mut reordered_coins);
    assert_ne!(reordered_coins, coins, "reordered cache must be detected");
}
