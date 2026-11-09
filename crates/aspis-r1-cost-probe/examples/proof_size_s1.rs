//! UNPROVED CANDIDATE. Proof-size test S1: exact stored bytes of three
//! layouts on the saved fixtures' actual query sets, plus the worst-case
//! node-count bound. usage: proof_size_s1 <fixture-dir>... (each holding
//! r1-s2-proof.bin and r1-s2-public-asf8.bin)
use aspis_core::{digest::LegacyHashFn, r0::merkle, state_only_private_merkle::private_leaf_hash_with_digest};
use aspis_prover::HOST_HASH;
use aspis_r1_cost_probe::{
    compact,
    multiproof::{self, Arity},
    r1_semantic,
    verifier::{self, Prepared, View, INITIAL_QUERY_BYTES},
};
use std::collections::HashMap;

type D = [u8; 32];

fn sha(parts: &[&[u8]]) -> D {
    HOST_HASH(parts)
}

/// Shipped per-query layout offsets (private-leaf-salts).
const C1_PATH: usize = 672;
const C2_PATH: usize = 672 + 1344;
const F_VALUES: usize = INITIAL_QUERY_BYTES;
const F_SALT: usize = F_VALUES + 128;
const F_PATH: usize = F_SALT + 32;

struct TreeOpen {
    leaves: Vec<(u32, D)>,
    nodes: HashMap<(u32, u32), D>,
}
impl TreeOpen {
    fn new() -> Self {
        Self { leaves: Vec::new(), nodes: HashMap::new() }
    }
    /// Record one shipped eight-way path for leaf `u`.
    fn add(&mut self, u: u32, leaf: D, path: &[u8]) {
        self.leaves.push((u, leaf));
        let mut index = u;
        for d in 0..6u32 {
            let slot = index % 8;
            let mut j = 0;
            for s in 0..8u32 {
                if s == slot {
                    continue;
                }
                let at = (d as usize) * 224 + j * 32;
                let digest: D = path[at..at + 32].try_into().unwrap();
                self.nodes.insert((d, index / 8 * 8 + s), digest);
                j += 1;
            }
            index /= 8;
        }
    }
}

/// Distinct sorted (index, leaf) of one batch; panics on inconsistent duplicates.
fn batch(leaves: &[(u32, D)]) -> (Vec<u32>, Vec<D>) {
    let mut idx: Vec<u32> = leaves.iter().map(|x| x.0).collect();
    let mut val: Vec<D> = leaves.iter().map(|x| x.1).collect();
    let n = multiproof::sort_dedup(&mut idx, &mut val).expect("consistent batch");
    idx.truncate(n);
    val.truncate(n);
    (idx, val)
}

fn main() {
    assert!(!cfg!(debug_assertions), "release build required");
    let hash = LegacyHashFn(HOST_HASH);
    let args: Vec<String> = std::env::args().skip(1).collect();
    // Synthetic binary tree, used only to exercise the binary encoder/verifier
    // walk on each fixture's index sets (node counts depend on indices only).
    let synthetic_leaves: Vec<D> = (0..1u32 << 18).map(|i| sha(&[b"s1-synthetic-leaf", &i.to_le_bytes()])).collect();
    let synthetic = multiproof::BinaryTree::new(hash, synthetic_leaves.clone()).unwrap();
    let mut fixtures = Vec::new();
    for dir in &args {
        let proof = std::fs::read(format!("{dir}/r1-s2-proof.bin")).unwrap();
        let public_bytes = std::fs::read(format!("{dir}/r1-s2-public-asf8.bin")).unwrap();
        let statement = aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&public_bytes).unwrap();
        let public = statement.semantic_public();
        // Shipped verifier accepts the fixture (control).
        let checkpoint = verifier::tx1(public, &public_bytes, &proof, compact::SPLIT, hash, None).unwrap();
        verifier::tx2(&public_bytes, &proof, &checkpoint, hash, None).unwrap();
        let v = View::parse(&proof).unwrap();
        let sem = r1_semantic::verify(public, v.semantic, hash).unwrap();
        let mut g = [aspis_core::field::WideExact::ZERO; 29];
        let p = Prepared::new(&sem, &v, hash, &mut g).unwrap();
        let queries = p.queries;

        // Layout A: compact only (shipped per-query paths kept).
        let mut a = proof[..verifier::HEADER].to_vec();
        compact::compact_semantic(v.semantic, &mut a).unwrap();
        compact::compact_values(v.y1, &mut a).unwrap();
        let tail_start = verifier::HEADER + verifier::SEMANTIC_BYTES + 29 * 32;
        a.extend_from_slice(&proof[tail_start..]);
        // Decoder round trip back to the shipped bytes.
        let mut back = proof[..verifier::HEADER].to_vec();
        let mut sem_l = vec![0u8; compact::LOGICAL_SEMANTIC];
        compact::expand_semantic(&a[compact::OFF_SEMANTIC..compact::OFF_Y1], &mut sem_l).unwrap();
        let mut y1_l = vec![0u8; compact::LOGICAL_Y1];
        compact::expand_values(&a[compact::OFF_Y1..compact::OFF_INACTIVE], &mut y1_l).unwrap();
        back.extend_from_slice(&sem_l);
        back.extend_from_slice(&y1_l);
        back.extend_from_slice(&a[compact::OFF_INACTIVE..]);
        assert_eq!(back, proof, "compact codec round trip");

        // Per-tree leaves and shipped paths.
        let mut trees = [TreeOpen::new(), TreeOpen::new(), TreeOpen::new()];
        for (i, &u) in queries.iter().enumerate() {
            let q = v.query(i);
            let c1 = private_leaf_hash_with_digest(hash, merkle::C1_TAG, &q[..480], q[608..640].try_into().unwrap());
            let c2 = private_leaf_hash_with_digest(hash, merkle::C2_TAG, &q[480..608], q[640..672].try_into().unwrap());
            let f = private_leaf_hash_with_digest(hash, 0x72, &q[F_VALUES..F_SALT], q[F_SALT..F_PATH].try_into().unwrap());
            trees[0].add(u, c1, &q[C1_PATH..C2_PATH]);
            trees[1].add(u, c2, &q[C2_PATH..INITIAL_QUERY_BYTES]);
            trees[2].add(u / 4, f, &q[F_PATH..]);
        }
        let roots = [p.roots[0], p.roots[1], *v.folded_root.unwrap()];
        // Layout B (eight-way multiproofs, real nodes from the shipped paths)
        // and layout C (binary counts, walk checked on the synthetic tree).
        let mut eight = [[0usize; 3]; 2];
        let mut two = [[0usize; 3]; 2];
        let mut distinct = [[0usize; 3]; 2];
        let mut b_nodes = Vec::new();
        for (bi, range) in [(0usize, 0..compact::SPLIT), (1, compact::SPLIT..22)] {
            for t in 0..3 {
                let (idx, val) = batch(&trees[t].leaves[range.clone()]);
                distinct[bi][t] = idx.len();
                let nodes = multiproof::generate(Arity::Eight, &idx, |l, i| trees[t].nodes[&(l, i)]).unwrap();
                assert!(multiproof::verify(hash, Arity::Eight, &roots[t], &idx, &val, &nodes), "eight-way multiproof");
                eight[bi][t] = nodes.len() / 32;
                b_nodes.extend_from_slice(&nodes);
                let bin = synthetic.multiproof(&idx).unwrap();
                let syn: Vec<D> = idx.iter().map(|&i| synthetic_leaves[i as usize]).collect();
                assert!(multiproof::verify(hash, Arity::Two, &synthetic.root(), &idx, &syn, &bin));
                two[bi][t] = bin.len() / 32;
                assert_eq!(two[bi][t], multiproof::node_count(Arity::Two, &idx).unwrap());
                assert!(two[bi][t] <= compact::SLOT_NODES[3 * bi + t]);
            }
        }
        let b_len = compact::FIXED + b_nodes.len();
        let e: usize = eight.iter().flatten().sum();
        let n2: usize = two.iter().flatten().sum();
        let c_len = compact::FIXED + 32 * n2;
        let folded_duplicates = 22 - distinct[0][2] - distinct[1][2];
        fixtures.push(serde_json::json!({
            "fixture": dir,
            "shipped_bytes": proof.len(),
            "queries": queries.to_vec(),
            "folded_duplicate_indices": folded_duplicates,
            "layout_compact_only_bytes": a.len(),
            "layout_eight_way_multiproof_compact_bytes": b_len,
            "eight_way_nodes": {"batchA_c1_c2_folded": eight[0], "batchB_c1_c2_folded": eight[1], "total": e},
            "layout_binary_multiproof_compact_variable_bytes": c_len,
            "layout_binary_multiproof_compact_padded_bytes": compact::PROOF_BYTES,
            "binary_nodes": {"batchA_c1_c2_folded": two[0], "batchB_c1_c2_folded": two[1], "total": n2},
        }));
    }

    // Worst case. Bound: nodes(I) = sum_{l=1}^{L-1} n_l + w*n_L - n_0 for the
    // binary/eight-way walk (w = arity, L levels), with n_l <= min(n_0,
    // capacity_l); maximal at n_0 = |batch| distinct leaves. Exhibited by
    // bit-reversed index sets, and checked against random sets.
    let spread = |k: u32, bits: u32| -> Vec<u32> {
        let mut v: Vec<u32> = (0..k).map(|j| j.reverse_bits() >> (32 - bits)).collect();
        v.sort();
        v
    };
    let bound = |a: Arity, k: usize, bits: u32| -> usize {
        // capacity of level l (in arity-steps) inside the first 2^bits leaves
        let levels = a.levels();
        let mut n = vec![0usize; levels as usize + 1];
        for l in 0..=levels {
            let cap_bits = bits as i64 - (l * a.bits()) as i64;
            n[l as usize] = if cap_bits <= 0 { 1 } else { k.min(1 << cap_bits) };
        }
        let mut s = 0;
        for l in 0..levels as usize {
            s += a.width() * n[l + 1] - n[l];
        }
        s
    };
    let mut worst = serde_json::Map::new();
    for (name, a) in [("binary", Arity::Two), ("eight_way", Arity::Eight)] {
        let mut total = 0;
        let mut rows = Vec::new();
        for (k, bits, tree) in [(10, 18, "C1 A"), (10, 18, "C2 A"), (10, 16, "folded A"), (12, 18, "C1 B"), (12, 18, "C2 B"), (12, 16, "folded B")] {
            let b = bound(a, k as usize, bits);
            assert_eq!(multiproof::node_count(a, &spread(k, bits)), Some(b), "{name} {tree} attained");
            total += b;
            rows.push(serde_json::json!({"slot": tree, "leaves": k, "domain_bits": bits, "bound_nodes": b}));
        }
        // Random index sets never exceed the bound.
        let mut ctr = 0u64;
        let mut max_seen = 0;
        for _ in 0..20000 {
            let mut sum = 0;
            for (k, bits) in [(10u32, 18u32), (10, 18), (10, 16), (12, 18), (12, 18), (12, 16)] {
                let mut set = Vec::new();
                while set.len() < k as usize {
                    let r = sha(&[b"s1-random", &ctr.to_le_bytes()]);
                    ctr += 1;
                    let x = u32::from_le_bytes(r[..4].try_into().unwrap()) >> (32 - bits);
                    set.push(x);
                }
                set.sort();
                set.dedup();
                sum += multiproof::node_count(a, &set).unwrap();
            }
            max_seen = max_seen.max(sum);
        }
        assert!(max_seen <= total);
        worst.insert(name.into(), serde_json::json!({
            "slots": rows, "bound_nodes": total, "bound_bytes": compact::FIXED + 32 * total,
            "random_sets_checked": 20000, "random_max_nodes": max_seen,
        }));
    }
    let out = serde_json::json!({
        "fixed_bytes_before_nodes": compact::FIXED,
        "candidate_padded_fixed_length_bytes": compact::PROOF_BYTES,
        "slot_nodes": compact::SLOT_NODES,
        "fixtures": fixtures,
        "worst_case": worst,
    });
    println!("{}", serde_json::to_string_pretty(&out).unwrap());
}
