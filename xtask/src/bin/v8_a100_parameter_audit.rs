//! Exact, source-tied V8-A100 parameter audit.
//!
//! Integer/rational fields in the JSON are emitted as decimal strings.  Only
//! the human-facing `*_bits` fields use floating-point arithmetic.

use aspis_core::{
    v6_onefold::{binary_frontier_nodes, V6_FIXED_QM31_VALUES, V6_WORK_NONCE_BYTES},
    v7_onefold::{
        V7_COMPACT_C1_BYTES_PER_QUERY, V7_COMPACT_C2_BYTES_PER_QUERY, V7_COMPACT_DIGEST_BYTES,
        V7_COMPACT_MAX_BODY_BYTES, V7_COMPACT_PRIVATE_SALT_BYTES, V7_COMPACT_QUERY_BYTES,
    },
    v8_a100::{maximum_binary_frontier, V8_A100_MAX_FRONTIER_FIXTURE, V8_A100_PROFILE_BINDING},
};
use aspis_statement::pool_v1::{
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES,
};
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};
use serde_json::{json, Value};

const DOMAIN_SIZE: usize = 1 << 18;
const BAD_AGREEMENT_SET: usize = 9_557;
const COMPONENTS: usize = 29;
const P: u32 = 2_147_483_647;

// This is a deliberately named research envelope, not a source theorem.  The
// current exact V7 compiler leaves Q and R parameterised.  Q=2^36 covers the
// three visible honest work spaces (2^35 + 2^31 + 2^34) with room for the
// non-work transcript calls; R=259 is the smallest integer satisfying every
// current `518 <= 2 * forkRequestCap` capstone premise.  The JSON keeps this
// provenance explicit so these conditional figures cannot be mistaken for a
// deployed resource certificate.
const RESEARCH_Q1_SHA_CALL_CAP: usize = 1usize << 36;
const RESEARCH_FORK_REQUEST_CAP: usize = 259;
const FULL256_VERIFIER_CALL_CAP: usize = 1_511;
const VISIBLE_HONEST_WORK: usize = (1usize << 35) + (1usize << 31) + (1usize << 34);
const FIXED_K15_NUMERATOR: usize = 396_430;
const GAMMA_DEGREE: usize = COMPONENTS - 1;
// The verifier checks only the two gamma-dot OOD scalars.  Outside the
// two-point fingerprint-collision event, at most one of the <=100 fixed
// tuples matches both complete vectors; every other tuple contributes at
// most 28 roots.  We conservatively retain 100 * 28, covering the case where
// no tuple matches both vectors.
const SCALAR_DEEP_GAMMA_CARDINALITY: usize = TUPLE_LIST_CAP * GAMMA_DEGREE;
const ONE_FOLD_NUMERATOR: usize = 3;
const LATER_ALPHA_NUMERATOR: usize = 18;
const TUPLE_LIST_CAP: usize = 100;
const CLEARED_COMPONENT_DEGREE: usize = 1_024;

#[derive(Clone)]
struct Rational {
    numerator: BigUint,
    denominator: BigUint,
}

impl Rational {
    fn new(numerator: BigUint, denominator: BigUint) -> Self {
        assert!(!denominator.is_zero());
        let gcd = numerator.gcd(&denominator);
        Self {
            numerator: numerator / &gcd,
            denominator: denominator / gcd,
        }
    }

    fn add(&self, other: &Self) -> Self {
        Self::new(
            &self.numerator * &other.denominator + &other.numerator * &self.denominator,
            &self.denominator * &other.denominator,
        )
    }

    fn sub_nonnegative(&self, other: &Self) -> Option<Self> {
        let left = &self.numerator * &other.denominator;
        let right = &other.numerator * &self.denominator;
        (left >= right).then(|| Self::new(left - right, &self.denominator * &other.denominator))
    }

    fn mul_biguint(&self, factor: &BigUint) -> Self {
        Self::new(&self.numerator * factor, self.denominator.clone())
    }

    fn floor(&self) -> BigUint {
        &self.numerator / &self.denominator
    }

    fn from_usize_ratio(numerator: usize, denominator: BigUint) -> Self {
        Self::new(BigUint::from(numerator), denominator)
    }

    fn negative_log2(&self) -> f64 {
        self.denominator.to_f64().unwrap().log2() - self.numerator.to_f64().unwrap().log2()
    }

    fn approximate_value(&self) -> f64 {
        self.numerator.to_f64().unwrap() / self.denominator.to_f64().unwrap()
    }

    fn json(&self) -> Value {
        json!({
            "numerator": self.numerator.to_str_radix(10),
            "denominator": self.denominator.to_str_radix(10),
            "negative_log2_bits": self.negative_log2(),
        })
    }
}

fn choose(n: usize, k: usize) -> BigUint {
    if k > n {
        return BigUint::zero();
    }
    let k = k.min(n - k);
    let mut result = BigUint::one();
    for i in 0..k {
        result *= BigUint::from(n - i);
        result /= BigUint::from(i + 1);
    }
    result
}

fn query_probability(q: usize) -> Rational {
    Rational::new(choose(BAD_AGREEMENT_SET, q), choose(DOMAIN_SIZE, q))
}

fn query_probability_json(q: usize) -> Value {
    let binomial_numerator = choose(BAD_AGREEMENT_SET, q);
    let binomial_denominator = choose(DOMAIN_SIZE, q);
    let reduced = Rational::new(binomial_numerator.clone(), binomial_denominator.clone());
    json!({
        "expression": format!("C({BAD_AGREEMENT_SET},{q}) / C({DOMAIN_SIZE},{q})"),
        "binomial_numerator": binomial_numerator.to_str_radix(10),
        "binomial_denominator": binomial_denominator.to_str_radix(10),
        "reduced": reduced.json(),
    })
}

fn expected_frontier(q: usize, depth: u8) -> Rational {
    let n = 1usize << depth;
    let denominator = choose(n, q);
    let mut numerator = BigUint::zero();
    for level in 0..depth {
        let child_size = 1usize << level;
        let child_blocks = n / child_size;
        let empty_child = choose(n - child_size, q);
        let empty_sibling_pair = choose(n - 2 * child_size, q);
        numerator += BigUint::from(child_blocks) * (empty_child - empty_sibling_pair);
    }
    Rational::new(numerator, denominator)
}

fn expected_frontier_json(q: usize, depth: u8) -> Value {
    let expectation = expected_frontier(q, depth);
    json!({
        "numerator": expectation.numerator.to_str_radix(10),
        "denominator": expectation.denominator.to_str_radix(10),
        "approximate_nodes": expectation.approximate_value(),
    })
}

fn frontier_count<const Q: usize>(queries: [u32; Q]) -> usize {
    binary_frontier_nodes(queries, 18).expect("fixture is valid")
}

fn fixed_qm31_values(ood_points: usize) -> usize {
    V6_FIXED_QM31_VALUES - 2 + ood_points * COMPONENTS
}

fn packed_m31_bytes(limbs: usize) -> usize {
    (31 * limbs + 7) / 8
}

fn research_compiler_caps() -> (usize, usize) {
    let q = RESEARCH_Q1_SHA_CALL_CAP;
    let r = RESEARCH_FORK_REQUEST_CAP;
    let f = q + FULL256_VERIFIER_CALL_CAP + r * (q + FULL256_VERIFIER_CALL_CAP) + 2 * r;
    let g = q + FULL256_VERIFIER_CALL_CAP + r * (2 * q + FULL256_VERIFIER_CALL_CAP);
    (f, g)
}

fn maximum_gamma_numerator(q: usize, digest_bytes: usize, target_bits: usize) -> Option<BigUint> {
    let field = BigUint::from(P).pow(4);
    let nonzero_field = &field - BigUint::one();
    let secure_circle_parameters = &field - BigUint::from(P).pow(2);
    let algebraic_without_gamma =
        ONE_FOLD_NUMERATOR + q + LATER_ALPHA_NUMERATOR + FIXED_K15_NUMERATOR;
    let deep_denominator = &secure_circle_parameters * (&secure_circle_parameters - 1u8);
    let (fresh_exposures, global_calls) = research_compiler_caps();
    let other = query_probability(q)
        .add(&Rational::from_usize_ratio(
            algebraic_without_gamma,
            nonzero_field.clone(),
        ))
        .add(&Rational::from_usize_ratio(
            TUPLE_LIST_CAP * TUPLE_LIST_CAP * CLEARED_COMPONENT_DEGREE * CLEARED_COMPONENT_DEGREE,
            deep_denominator,
        ))
        .add(&Rational::new(
            BigUint::from(FULL256_VERIFIER_CALL_CAP * 2 * q) + choose(fresh_exposures, 2),
            BigUint::one() << (8 * digest_bytes),
        ))
        .add(&Rational::new(
            BigUint::from(fresh_exposures)
                + choose(fresh_exposures, 2)
                + BigUint::from(fresh_exposures) * BigUint::from(global_calls),
            BigUint::one() << 256usize,
        ));
    Rational::new(BigUint::one(), BigUint::one() << target_bits)
        .sub_nonnegative(&other)
        .map(|remaining| remaining.mul_biguint(&nonzero_field).floor())
}

fn full_raw_ledger(q: usize, digest_bytes: usize) -> Value {
    let field = BigUint::from(P).pow(4);
    let nonzero_field = &field - BigUint::one();
    let secure_circle_parameters = &field - BigUint::from(P).pow(2);
    let query = query_probability(q);
    let algebraic_numerator = ONE_FOLD_NUMERATOR
        + q
        + LATER_ALPHA_NUMERATOR
        + FIXED_K15_NUMERATOR
        + SCALAR_DEEP_GAMMA_CARDINALITY;
    let algebraic = Rational::from_usize_ratio(algebraic_numerator, nonzero_field);
    let deep_numerator =
        TUPLE_LIST_CAP * TUPLE_LIST_CAP * CLEARED_COMPONENT_DEGREE * CLEARED_COMPONENT_DEGREE;
    let deep_denominator = &secure_circle_parameters * (&secure_circle_parameters - 1u8);
    let deep = Rational::from_usize_ratio(deep_numerator, deep_denominator);

    let (fresh_exposures, global_calls) = research_compiler_caps();
    let k12_numerator =
        BigUint::from(FULL256_VERIFIER_CALL_CAP * 2 * q) + choose(fresh_exposures, 2);
    let k12 = Rational::new(k12_numerator, BigUint::one() << (8 * digest_bytes));
    let compiler_numerator = BigUint::from(fresh_exposures)
        + choose(fresh_exposures, 2)
        + BigUint::from(fresh_exposures) * BigUint::from(global_calls);
    let compiler = Rational::new(compiler_numerator, BigUint::one() << 256usize);
    let total = query.add(&algebraic).add(&deep).add(&k12).add(&compiler);
    let proves_100 = &total.numerator * (BigUint::one() << 100usize) <= total.denominator;
    let proves_104 = &total.numerator * (BigUint::one() << 104usize) <= total.denominator;

    json!({
        "status": "conditional: exact arithmetic under the named research Q/R envelope; current source theorem leaves Q and R symbolic",
        "research_resource_envelope": {
            "q1_sha_call_cap": RESEARCH_Q1_SHA_CALL_CAP.to_string(),
            "fork_request_cap": RESEARCH_FORK_REQUEST_CAP,
            "full256_verifier_call_cap": FULL256_VERIFIER_CALL_CAP,
            "visible_honest_work": VISIBLE_HONEST_WORK.to_string(),
            "visible_honest_work_fits_q": VISIBLE_HONEST_WORK < RESEARCH_Q1_SHA_CALL_CAP,
            "unified_fresh_exposures_F": fresh_exposures.to_string(),
            "global_full256_calls_G": global_calls.to_string(),
        },
        "terms": {
            "query_consistency": query.json(),
            "algebraic_nonzero_qm31": {
                "numerator_breakdown": {
                    "one_fold": ONE_FOLD_NUMERATOR,
                    "query_batch": q,
                    "later_alpha": LATER_ALPHA_NUMERATOR,
                    "fixed_k15": FIXED_K15_NUMERATOR,
                    "scalar_deep_gamma": SCALAR_DEEP_GAMMA_CARDINALITY,
                },
                "total": algebraic.json(),
            },
            "two_point_tuple_collision": deep.json(),
            "k12_merkle_digest": k12.json(),
            "full256_compiler": compiler.json(),
        },
        "total": total.json(),
        "maximum_gamma_cardinality_compatible_with_target": {
            "100_bits": maximum_gamma_numerator(q, digest_bytes, 100)
                .map(|value| value.to_str_radix(10)),
            "104_bits": maximum_gamma_numerator(q, digest_bytes, 104)
                .map(|value| value.to_str_radix(10)),
        },
        "proves_100_bit_arithmetic_inequality": proves_100,
        "proves_104_bit_arithmetic_inequality": proves_104,
    })
}

fn profile_size(q: usize, digest_bytes: usize, ood_points: usize) -> Value {
    let fixed_qm31 = fixed_qm31_values(ood_points);
    let fixed_bytes = packed_m31_bytes(4 * fixed_qm31);
    let frontier = maximum_binary_frontier(18, q);
    let query_section = q * V7_COMPACT_QUERY_BYTES;
    let roots = 2 * digest_bytes;
    let body_without_frontiers = fixed_bytes + roots + V6_WORK_NONCE_BYTES + query_section;
    let maximum_body = body_without_frontiers + 2 * frontier * digest_bytes;
    let query_error = query_probability(q);

    // This intentionally excludes K1.2 resource-dependent hash terms and the
    // separately accounted two-point tuple-collision term.  It uses the
    // conservative scalar-DEEP bad-gamma cardinality 100 * 28.
    let p = BigUint::from(P);
    let field_nonzero = p.pow(4) - BigUint::one();
    let algebraic_numerator = BigUint::from(
        3usize + q + 18usize + 396_430usize + SCALAR_DEEP_GAMMA_CARDINALITY,
    );
    let optimistic = query_error.add(&Rational::new(algebraic_numerator, field_nonzero));

    json!({
        "q": q,
        "digest_bytes": digest_bytes,
        "digest_bits": 8 * digest_bytes,
        "ood_points": ood_points,
        "fixed_qm31_values": fixed_qm31,
        "fixed_packed_field_bytes": fixed_bytes,
        "c1_bytes_per_query": V7_COMPACT_C1_BYTES_PER_QUERY,
        "c2_bytes_per_query": V7_COMPACT_C2_BYTES_PER_QUERY,
        "salt_bytes_per_query": V7_COMPACT_PRIVATE_SALT_BYTES,
        "query_record_bytes": V7_COMPACT_QUERY_BYTES,
        "query_section_bytes": query_section,
        "root_bytes": roots,
        "work_nonce_bytes": V6_WORK_NONCE_BYTES,
        "maximum_frontier_per_tree": frontier,
        "expected_frontier_per_tree": expected_frontier_json(q, 18),
        "body_without_frontiers": body_without_frontiers,
        "maximum_proof_body": maximum_body,
        "proof_account_header": POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES,
        "candidate_afterstate_size": POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        "complete_pair_verifier_account_size": maximum_body
            + POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES
            + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
        "query_consistency": query_error.json(),
        "optimistic_algebraic_subtotal_excluding_k12_and_deep": optimistic.json(),
        "conditional_complete_raw_ledger": full_raw_ledger(q, digest_bytes),
        "raw_security_status": "arithmetic closed only under named research Q/R envelope; source resource instantiation and event composition remain open",
        "mask_profile": {
            "candidate": "unchanged production 26 M31 C1 columns plus 3 QM31 C2 columns",
            "enlargement_bytes": 0,
            "status": "concrete q22/two-OOD pair and pair-forest nonzero-minor witnesses; all-schedule/OOD surjectivity theorem remains open",
        },
    })
}

fn main() {
    assert_eq!(&V8_A100_PROFILE_BINDING[..8], b"AV8A1001");
    assert_eq!(V7_COMPACT_C1_BYTES_PER_QUERY, 403);
    assert_eq!(V7_COMPACT_C2_BYTES_PER_QUERY, 186);
    assert_eq!(V7_COMPACT_PRIVATE_SALT_BYTES, 32);
    assert_eq!(V7_COMPACT_QUERY_BYTES, 621);
    assert_eq!(V7_COMPACT_DIGEST_BYTES, 26);
    assert_eq!(V7_COMPACT_MAX_BODY_BYTES, 30_504);
    assert_eq!(POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES, 40);
    assert_eq!(POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, 688);

    let compact: [u32; 22] = core::array::from_fn(|i| i as u32);
    let typical = [
        231_696, 190_946, 246_950, 53_197, 7_289, 54_330, 114_496, 152_078, 187_153, 79_950,
        88_748, 246_054, 172_132, 101_489, 123_716, 95_860, 205_063, 89_983, 87_425, 129_527,
        252_951, 48_626,
    ];
    let high = [
        0, 8_192, 32_768, 49_152, 65_536, 81_920, 98_304, 114_688, 131_072, 147_456, 163_840,
        172_032, 180_224, 188_416, 196_608, 204_800, 212_992, 221_184, 229_376, 237_568, 245_760,
        253_952,
    ];

    let query_probabilities: Vec<Value> = (20..=24)
        .map(|q| json!({"q": q, "probability": query_probability_json(q)}))
        .collect();
    let frontier_maxima: Vec<Value> = (16..=24)
        .map(|q| {
            json!({
                "q": q,
                "maximum": maximum_binary_frontier(18, q),
                "expected": expected_frontier_json(q, 18),
            })
        })
        .collect();
    let mut sweep = Vec::new();
    for q in 21..=24 {
        for digest_bytes in [26usize, 27, 28, 32] {
            for ood_points in [2usize, 3] {
                sweep.push(profile_size(q, digest_bytes, ood_points));
            }
        }
    }

    let output = json!({
        "schema": "aspis-v8-a100-parameter-audit-v1",
        "source_tied_v7": {
            "fixed_qm31_values": V6_FIXED_QM31_VALUES,
            "c1_bytes_per_query": V7_COMPACT_C1_BYTES_PER_QUERY,
            "c2_bytes_per_query": V7_COMPACT_C2_BYTES_PER_QUERY,
            "salt_bytes_per_query": V7_COMPACT_PRIVATE_SALT_BYTES,
            "query_record_bytes": V7_COMPACT_QUERY_BYTES,
            "digest_bytes": V7_COMPACT_DIGEST_BYTES,
            "maximum_body": V7_COMPACT_MAX_BODY_BYTES,
        },
        "frontier_formula": "q*(depth-ceil_log2(q)) + (2^ceil_log2(q)-q)",
        "frontier_maxima": frontier_maxima,
        "q22_fixtures": [
            {"kind": "unusually_compact", "positions": compact, "frontier": frontier_count(compact)},
            {"kind": "deterministic_typical", "positions": typical, "frontier": frontier_count(typical)},
            {"kind": "high", "positions": high, "frontier": frontier_count(high)},
            {"kind": "exact_maximum", "positions": V8_A100_MAX_FRONTIER_FIXTURE,
                "frontier": frontier_count(V8_A100_MAX_FRONTIER_FIXTURE)},
        ],
        "query_probabilities": query_probabilities,
        "parameter_sweep": sweep,
    });
    let encoded = serde_json::to_string_pretty(&output).unwrap();
    let mut args = std::env::args().skip(1);
    match (args.next().as_deref(), args.next(), args.next()) {
        (None, None, None) => println!("{encoded}"),
        (Some("--write"), Some(path), None) => {
            let path = std::path::Path::new(&path);
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent).unwrap();
            }
            std::fs::write(path, format!("{encoded}\n")).unwrap();
            eprintln!("wrote {}", path.display());
        }
        _ => panic!("usage: v8_a100_parameter_audit [--write PATH]"),
    }
}
