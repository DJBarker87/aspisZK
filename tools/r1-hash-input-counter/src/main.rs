use aspis_r1_cost_probe::{transport::Variant, verifier};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{collections::HashMap, fs, path::Path, sync::{atomic::{AtomicU8, Ordering}, Mutex, OnceLock}};

#[derive(Default, Clone, Copy)]
struct Counts { tx1: u64, tx2: u64 }

#[derive(Clone, Copy)]
struct CountedDigest;
impl aspis_core::Digest32 for CountedDigest {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] { counted_hash(parts) }
}

static PHASE: AtomicU8 = AtomicU8::new(0);
static ORDERED: OnceLock<Mutex<Vec<Value>>> = OnceLock::new();
static INPUTS: OnceLock<Mutex<HashMap<Vec<u8>, Counts>>> = OnceLock::new();

fn counted_hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut input = Vec::new();
    for part in parts { input.extend_from_slice(part); }
    let phase = PHASE.load(Ordering::Relaxed);
    let mut map = INPUTS.get_or_init(|| Mutex::new(HashMap::new())).lock().unwrap();
    let counts = map.entry(input).or_default();
    match phase { 1 => counts.tx1 += 1, 2 => counts.tx2 += 1, _ => panic!("hash called outside tx1/tx2") }
    let output = aspis_prover::host_hashv(parts);
    ORDERED.get_or_init(|| Mutex::new(Vec::new())).lock().unwrap().push(json!({
        "phase": phase,
        "parts_hex": parts.iter().map(|part| hex(part)).collect::<Vec<_>>(),
        "output_hex": hex(&output),
    }));
    output
}

fn sha(bytes: &[u8]) -> String { format!("{:x}", Sha256::digest(bytes)) }

fn main() {
    assert!(!cfg!(debug_assertions), "counter must run in optimized release mode");
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(args.len(), 5, "usage: r1-hash-input-counter <proof> <public> <output.json> <source-revision>");
    let proof_path = Path::new(&args[1]);
    let public_path = Path::new(&args[2]);
    let output_path = Path::new(&args[3]);
    let proof = fs::read(proof_path).expect("read saved proof");
    let saved_public = fs::read(public_path).expect("read saved public bytes");
    assert!(!output_path.exists(), "output must be fresh");

    let statement = aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&saved_public)
        .expect("decode saved ASF8 public statement");
    let reconstructed = aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .expect("re-encode decoded ASF8 public statement");
    assert_eq!(saved_public, reconstructed, "saved public bytes do not round-trip through the existing ASF8 reconstruction helper");
    let public = aspis_prover::r0_fixture::statement_public(&statement);
    assert_eq!(proof[8], Variant::S2.tag(), "proof is not the two-fold S2 variant");

    // Default: the adopted compact binary-multiproof verifier (split 10).
    // `audit-eight-way`: the retired eight-way verifier (split 11, the
    // baseline of the 583-call ordered trace).
    #[cfg(not(feature = "audit-eight-way"))]
    let (format, magic, split) = ("compact binary-multiproof (adopted)", aspis_r1_cost_probe::compact::MAGIC, verifier::SPLIT);
    #[cfg(feature = "audit-eight-way")]
    let (format, magic, split) = ("eight-way (audit)", b"R1P3COST", 11);
    assert_eq!(&proof[..8], magic, "not a {format} P3 proof");
    #[cfg(not(feature = "audit-eight-way"))]
    use verifier::{tx1, tx2};
    #[cfg(feature = "audit-eight-way")]
    use verifier::eight_way::{tx1, tx2};

    PHASE.store(1, Ordering::Relaxed);
    let checkpoint = tx1(public, &saved_public, &proof, split, CountedDigest, None).expect("tx1 acceptance");
    PHASE.store(2, Ordering::Relaxed);
    tx2(&saved_public, &proof, &checkpoint, CountedDigest, None).expect("tx2 acceptance");
    PHASE.store(0, Ordering::Relaxed);

    let map = INPUTS.get().unwrap().lock().unwrap();
    let tx1_raw: u64 = map.values().map(|c| c.tx1).sum();
    let tx2_raw: u64 = map.values().map(|c| c.tx2).sum();
    let distinct_tx1 = map.values().filter(|c| c.tx1 > 0).count();
    let distinct_tx2 = map.values().filter(|c| c.tx2 > 0).count();
    let distinct_union = map.len();
    let repeated: Vec<Value> = map.iter().filter(|(_, c)| c.tx1 + c.tx2 > 1).map(|(input, c)| json!({
        "input_len": input.len(), "input_hex": hex(input), "input_sha256_annotation_only": sha(input),
        "tx1_calls": c.tx1, "tx2_calls": c.tx2, "total_calls": c.tx1 + c.tx2,
    })).collect();
    let report = json!({
        "scope": "host native verifier tx1+tx2 only; exact full concatenated input Vec<u8> used as identity",
        "source_revision": args[4],
        "verifier_format": format, "stage1_split": split,
        "fixture": {
            "proof_path": proof_path, "proof_len": proof.len(), "proof_sha256": sha(&proof),
            "public_path": public_path, "public_len": saved_public.len(), "public_sha256": sha(&saved_public),
            "public_reconstruction_equal": true, "variant": "S2 two-fold", "fixture_mode": "existing saved proof/public; no proof generation"
        },
        "acceptance": { "tx1": true, "tx2": true, "checkpoint_len": checkpoint.len(), "checkpoint_hex": hex(&checkpoint) },
        "ordered_digest_calls": *ORDERED.get().unwrap().lock().unwrap(),
        "hash_input_counts": {
            "tx1_raw_calls": tx1_raw, "tx1_distinct_inputs": distinct_tx1,
            "tx2_raw_calls": tx2_raw, "tx2_distinct_inputs": distinct_tx2,
            "combined_raw_calls": tx1_raw + tx2_raw, "combined_distinct_inputs": distinct_union,
            "repeat_calls_beyond_first_per_exact_input": tx1_raw + tx2_raw - distinct_union as u64,
            "repeated_exact_inputs": repeated
        },
        "identity_rule": "HashMap<Vec<u8>, Counts> keyed by the complete concatenated input bytes; SHA-256 is included only as a display annotation",
        "exclusions": ["fixture reconstruction", "public encoding", "proof parsing outside verifier hash calls", "prover execution"]
    });
    fs::write(output_path, serde_json::to_vec_pretty(&report).unwrap()).expect("write report");
}

fn hex(bytes: &[u8]) -> String { const H: &[u8;16] = b"0123456789abcdef"; let mut s=String::with_capacity(bytes.len()*2); for &b in bytes { s.push(H[(b>>4) as usize] as char); s.push(H[(b&15) as usize] as char); } s }
