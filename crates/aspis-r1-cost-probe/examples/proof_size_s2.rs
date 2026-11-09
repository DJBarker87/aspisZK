//! UNPROVED. Proof-size teeth (S2 measurement 5), re-pointed at the adopted
//! build (PREREG-PROOF-SIZE-2): the default prover's output on the
//! deterministic R0 fixture is accepted by the default verifier (and the
//! dense verifier), and every pre-registered mutation is rejected. The
//! eight-way control is a saved eight-way fixture (no eight-way prover exists
//! in a prover build any more).
use aspis_core::{digest::LegacyHashFn, Digest32, HashFn};
use aspis_prover::HOST_HASH;
use aspis_r1_cost_probe::{
    compact, prover,
    transport::Variant,
    verifier::{self, candidate, Error},
};

fn main() {
    assert!(!cfg!(debug_assertions), "release build required");
    let raw: HashFn = HOST_HASH;
    let hash = LegacyHashFn(raw);
    let fixture = aspis_prover::r0_fixture::prepare(false);
    let public = aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&fixture.statement).unwrap();
    let seed = raw(&[b"UNPROVED:R1:proof-size-s2", &public]);
    let start = std::time::Instant::now();
    let (proof, _) = prover::prove_masked_fixture(fixture.public(), &fixture.compiled, Variant::S2, raw, &seed).unwrap();
    let prove_seconds = start.elapsed().as_secs_f64();
    assert_eq!(proof.len(), compact::PROOF_BYTES);
    assert_eq!(proof.len(), verifier::PROOF_BYTES);
    aspis_r1_cost_probe::dense::verify(fixture.public(), &proof, raw).expect("dense verifier accepts");
    // Eight-way control: a saved retired-format S2 proof (124,343 bytes).
    let shipped: &[u8] = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"),
        "/../../docs/research/100bit-spend-path-20261013/evidence/p3-private-leaf-salts-20261013/p3-pool-13/transfer-1023-os-task/r1-s2-proof.bin"));
    assert_eq!(shipped.len(), 124_343);

    // `candidate::*` are the default `verifier::*` entrypoints (re-exports).
    let tx1 = |p: &[u8]| candidate::tx1(fixture.public(), &public, p, compact::SPLIT, hash, None);
    let ck = tx1(&proof).expect("candidate stage 1 accepts");
    assert_eq!(ck.len(), verifier::checkpoint_size(Variant::S2));
    candidate::tx2_authenticated(&public, &proof, &ck, hash, None).expect("candidate stage 2 accepts");
    candidate::tx2(&public, &proof, &ck, hash, None).expect("candidate strict stage 2 accepts");
    // Both stages, on a proof mutated so that stage 1 still passes.
    let both = |p: &[u8]| -> Result<(), Error> {
        let c = tx1(p)?;
        candidate::tx2_authenticated(&public, p, &c, hash, None)
    };
    let used = |s: usize| -> usize {
        // real nodes in slot s = slot size minus trailing zero 32-byte words
        let slot = &proof[compact::slot_offset(s)..compact::slot_offset(s + 1)];
        slot.chunks(32).rposition(|c| c.iter().any(|&b| b != 0)).map_or(0, |i| i + 1)
    };
    let counts: Vec<usize> = (0..6).map(used).collect();
    let mut results = Vec::new();
    let mut expect_any = |name: &str, got: Result<(), Error>, want: Option<Error>| {
        match want {
            Some(w) => assert_eq!(got, Err(w), "{name}"),
            None => assert!(got.is_err(), "{name}"),
        }
        results.push(serde_json::json!({"mutation": name, "result": format!("{:?}", got)}));
    };
    macro_rules! expect {
        ($n:expr, $g:expr, $w:expr) => { expect_any(&$n, $g, Some($w)) };
    }
    let flip = |at: usize| {
        let mut p = proof.clone();
        p[at] ^= 1;
        p
    };
    // 1. Wrong sibling hash, batch A (stage 1) and batch B (stage 2).
    for s in 0..6 {
        let at = compact::slot_offset(s) + 32 * (counts[s] / 2) + 7;
        expect!(&format!("wrong sibling, slot {s}"), both(&flip(at)), Error::Merkle);
    }
    // 2. Missing node: last real node of a slot removed (the slot then holds
    // one node fewer, the rest is padding).
    for s in [0, 2, 3, 5] {
        let mut p = proof.clone();
        let at = compact::slot_offset(s) + 32 * (counts[s] - 1);
        p[at..at + 32].fill(0);
        expect!(&format!("missing node, slot {s}"), both(&p), Error::Merkle);
    }
    // 3. Extra node: a non-zero word right after the real nodes.
    for s in [0, 4] {
        let mut p = proof.clone();
        let at = compact::slot_offset(s) + 32 * counts[s];
        p[at..at + 32].fill(0xa5);
        expect!(&format!("extra node, slot {s}"), both(&p), Error::Parse);
    }
    // Any non-zero padding byte, last byte of the last slot.
    expect!("non-zero padding byte", both(&flip(compact::PROOF_BYTES - 1)), Error::Parse);
    // 4. Duplicated / misordered leaf index: openings swapped between two
    // queries of one batch (each leaf then sits at another index), and one
    // opening duplicated over another.
    let open = |i: usize| compact::OFF_OPENINGS + i * compact::OPENING;
    for (i, j, batch) in [(0, 1, "A"), (11, 20, "B")] {
        let mut p = proof.clone();
        let (a, b) = (open(i), open(j));
        let qi = proof[a..a + compact::OPENING].to_vec();
        let qj = proof[b..b + compact::OPENING].to_vec();
        p[a..a + compact::OPENING].copy_from_slice(&qj);
        p[b..b + compact::OPENING].copy_from_slice(&qi);
        expect!(&format!("misordered leaves {i}<->{j}, batch {batch}"), both(&p), Error::Merkle);
        let mut d = proof.clone();
        d[b..b + compact::OPENING].copy_from_slice(&qi);
        expect!(&format!("duplicated leaf {i}->{j}, batch {batch}"), both(&d), Error::Merkle);
    }
    // 5. Non-zero byte where a compact field's zero half is implied.
    // (a) The stored form has no high half: a proof that carries a semantic
    // value in its 32-byte form with a non-zero high byte has the wrong
    // length and fails the strict parse.
    let mut wide = proof[..compact::OFF_SEMANTIC + 32 + 5 * 15 + 32].to_vec();
    let rest = &proof[wide.len()..];
    wide.extend_from_slice(&rest[..16]);
    wide.extend_from_slice(&[1u8; 16]);
    wide.extend_from_slice(&rest[16..]);
    expect!("semantic value stored wide with non-zero high half", tx1(&wide).map(|_| ()), Error::Parse);
    // (b) Same for y1, keeping the total length (last padding word dropped).
    let mut y = proof[..compact::OFF_Y1 + 16].to_vec();
    y.extend_from_slice(&[1u8; 16]);
    y.extend_from_slice(&proof[compact::OFF_Y1 + 16..compact::PROOF_BYTES - 16]);
    assert_eq!(y.len(), compact::PROOF_BYTES);
    expect_any("y1 value with injected high half (length kept)", tx1(&y).map(|_| ()), None);
    // (c) The decoder rebuilds zero halves: a logical record with a non-zero
    // high byte has no compact encoding (encoder refuses).
    let mut logical = vec![0u8; compact::LOGICAL_SEMANTIC];
    compact::expand_semantic(&proof[compact::OFF_SEMANTIC..compact::OFF_Y1], &mut logical).unwrap();
    let last_value = compact::LOGICAL_SEMANTIC - 32;
    let mut forged = logical.clone();
    forged[last_value + 20] = 1;
    assert_eq!(compact::compact_semantic(&forged, &mut Vec::new()), Err(compact::CodecError::NonZeroHigh));
    let encoder_refusal = serde_json::json!({"mutation": "encoder: logical semantic value with non-zero high half", "result": "Err(NonZeroHigh)"});
    // (d) Non-canonical compact limb (2^31-1) in a semantic row and in y1.
    // The semantic value is rejected by the shipped Prefix::parse after the
    // rebuild (Semantic); the y1 value by the strict scan (Parse).
    for (name, at, want) in [("non-canonical compact semantic limb", compact::OFF_SEMANTIC + 32 + 5 * 15 + 32, Error::Semantic), ("non-canonical compact y1 limb", compact::OFF_Y1, Error::Parse)] {
        let mut p = proof.clone();
        p[at..at + 4].copy_from_slice(&0x7fff_ffffu32.to_le_bytes());
        expect!(name, tx1(&p).map(|_| ()), want);
    }
    // 6. Checkpoint over the expanded rather than the compact bytes.
    let mut expanded = proof[..compact::HEADER].to_vec();
    expanded.extend_from_slice(&logical);
    let mut y1l = vec![0u8; compact::LOGICAL_Y1];
    compact::expand_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE], &mut y1l).unwrap();
    expanded.extend_from_slice(&y1l);
    expanded.extend_from_slice(&proof[compact::OFF_INACTIVE..]);
    let mut bad_ck = ck.clone();
    bad_ck[16..48].copy_from_slice(&hash.digest(&[&expanded]));
    let end = bad_ck.len() - 32;
    let sum = hash.digest(&[b"UNPROVED:R1:checkpoint", &bad_ck[..end]]);
    bad_ck[end..].copy_from_slice(&sum);
    expect!("checkpoint over expanded bytes", candidate::tx2_authenticated(&public, &proof, &bad_ck, hash, None), Error::Checkpoint);
    expect!("expanded bytes presented as the proof", candidate::tx2_authenticated(&public, &expanded, &bad_ck, hash, None), Error::Parse);
    // Other strictness: wrong split, shipped proof to candidate, candidate to
    // shipped, a semantic byte changed after stage 1.
    expect!("stage 1 split 11", candidate::tx1(fixture.public(), &public, &proof, 11, hash, None).map(|_| ()), Error::Parse);
    expect!("eight-way proof to adopted verifier", tx1(shipped).map(|_| ()), Error::Parse);
    expect!("eight-way proof to adopted verifier, split 11", verifier::tx1(fixture.public(), &public, shipped, 11, hash, None).map(|_| ()), Error::Parse);
    expect!("proof changed after stage 1", candidate::tx2_authenticated(&public, &flip(compact::OFF_SEMANTIC + 40), &ck, hash, None), Error::Checkpoint);
    results.push(encoder_refusal);
    let out = serde_json::json!({
        "candidate_bytes": proof.len(), "shipped_bytes": shipped.len(),
        "slot_real_nodes": counts, "slot_capacity": compact::SLOT_NODES,
        "candidate_prove_seconds": prove_seconds,
        "accepted": ["default tx1", "default tx2_authenticated", "default tx2 strict", "dense"],
        "rejections": results,
    });
    println!("{}", serde_json::to_string_pretty(&out).unwrap());
}
