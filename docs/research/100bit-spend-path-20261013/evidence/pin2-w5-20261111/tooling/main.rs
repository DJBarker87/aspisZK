//! LEAD TOOLING (PIN2 W5). Not shipped source. Runs the pinned verifier
//! library (crates/aspis-r1-cost-probe) exactly as the pool-adapter stage-1
//! and stage-2 routes call it, on recorded input files, and prints:
//!   V <stage> <seq> <tag> <index> <32-byte hex>     every trace::value, in order
//!   H <stage> <seq> <part lengths> <input hex> <output hex>  every SHA-256 call
//!   R <key> <value>                                  results and checks
//! Usage: pin2-w5-dump <statement.bin> <proof.bin> <recorded-checkpoint.bin> <k>
use aspis_core::Digest32;
use aspis_r1_cost_probe::{trace, verifier};
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_terminal_statement_v1, encode_pool_v1_pair_forest_terminal_statement_v1,
    validate_pool_v1_pair_forest_terminal_statement_v1,
};
use sha2::{Digest, Sha256};
use std::cell::RefCell;

thread_local! { static CALLS: RefCell<Vec<(Vec<usize>, Vec<u8>, [u8; 32])>> = const { RefCell::new(Vec::new()) }; }

/// Same digest as the program's SolanaDigest (hashv = SHA-256 over the
/// concatenated parts); records each call.
#[derive(Clone, Copy)]
struct Recording;
impl Digest32 for Recording {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
        let mut h = Sha256::new();
        let mut input = Vec::new();
        for p in parts { h.update(p); input.extend_from_slice(p); }
        let out: [u8; 32] = h.finalize().into();
        CALLS.with(|c| c.borrow_mut().push((parts.iter().map(|p| p.len()).collect(), input, out)));
        out
    }
}
fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }
fn sha(b: &[u8]) -> String { hex(&Sha256::digest(b)) }
fn flush(stage: &str) {
    for (i, (tag, index, x)) in trace::take().into_iter().enumerate() {
        println!("V {stage} {i} {tag} {index} {}", hex(&x));
    }
    CALLS.with(|c| {
        for (i, (lens, input, out)) in core::mem::take(&mut *c.borrow_mut()).into_iter().enumerate() {
            let l: Vec<String> = lens.iter().map(|x| x.to_string()).collect();
            println!("H {stage} {i} {} {} {}", l.join(","), hex(&input), hex(&out));
        }
    });
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    assert_eq!(a.len(), 5, "usage: pin2-w5-dump <statement.bin> <proof.bin> <recorded-checkpoint.bin> <k>");
    let statement_bytes = std::fs::read(&a[1]).unwrap();
    let proof = std::fs::read(&a[2]).unwrap();
    let recorded = std::fs::read(&a[3]).unwrap();
    let k: usize = a[4].parse().unwrap();
    println!("R statement_sha256 {}", sha(&statement_bytes));
    println!("R proof_sha256 {}", sha(&proof));
    println!("R recorded_checkpoint_sha256 {}", sha(&recorded));
    println!("R debug_assertions {}", cfg!(debug_assertions));
    // Stage 1 as r1_pool_adapter_owned::stage1_owned: decode, validate,
    // semantic_public(), public_bytes = the statement account bytes.
    let statement = decode_pool_v1_pair_forest_terminal_statement_v1(&statement_bytes).expect("decode");
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement).expect("validate");
    let reencoded = encode_pool_v1_pair_forest_terminal_statement_v1(&statement).expect("encode");
    println!("R statement_reencode_equal {}", statement_bytes == reencoded);
    let public_bytes = statement.semantic_public().public_bytes().expect("public_bytes");
    println!("R semantic_public_bytes_len {}", public_bytes.len());
    println!("R semantic_public_bytes {}", hex(&public_bytes));
    trace::take();
    CALLS.with(|c| c.borrow_mut().clear());
    let checkpoint = verifier::tx1(statement.semantic_public(), &statement_bytes, &proof, k, Recording, None).expect("stage 1");
    flush("tx1");
    println!("R tx1_checkpoint_len {}", checkpoint.len());
    println!("R tx1_checkpoint_sha256 {}", sha(&checkpoint));
    println!("R tx1_checkpoint {}", hex(&checkpoint));
    println!("R tx1_checkpoint_equals_recorded {}", checkpoint == recorded);
    // Stage 2 as stage2_owned: tx2_authenticated over the encoded statement
    // (equal to the account bytes, checked above) and the RECORDED checkpoint.
    let r2 = verifier::tx2_authenticated(&reencoded, &proof, &recorded, Recording, None);
    flush("tx2");
    println!("R tx2_result {:?}", r2);
    // Strict stage 2 (full canonical scan) as a second check.
    let r3 = verifier::tx2(&reencoded, &proof, &recorded, Recording, None);
    trace::take();
    CALLS.with(|c| c.borrow_mut().clear());
    println!("R tx2_strict_result {:?}", r3);
    assert!(checkpoint == recorded && r2.is_ok() && r3.is_ok(), "STOP: native run does not reproduce the recorded run");
}
