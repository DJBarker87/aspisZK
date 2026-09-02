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
    // not-yet-established two-point tuple-separation term.  It is the exact
    // optimistic algebraic subtotal under bad-gamma cardinality 28.
    let p = BigUint::from(2_147_483_647u32);
    let field_nonzero = p.pow(4) - BigUint::one();
    let algebraic_numerator = BigUint::from(3usize + q + 18usize + 396_430usize + 28usize);
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
        "raw_security_status": "unclosed: excludes exact K1.2 resources and two-point candidate separation",
        "hiding_status": "unclosed: existing six-mask probe covers only one frozen q16 schedule",
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
