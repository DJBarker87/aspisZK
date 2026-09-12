//! Exact-source authentication control for the finite-prefix access adapter.
//! Synthetic, consistent full-answer tables are NOT SHA/ROM distribution tests.
//! This builds only the 521 required records, not the full committed tree.
#![allow(dead_code)]
extern crate alloc;
use std::{cell::RefCell, collections::BTreeMap};
#[path = "../../../crates/aspis-core/src/field.rs"] pub mod field;
mod corelib { pub use crate::field; }
use field::M31;
pub type HashFn = fn(&[&[u8]]) -> [u8; 32];
mod transcript { pub type HashFn = crate::HashFn; }
#[path = "../../../crates/aspis-core/src/state_only_private_merkle.rs"]
mod state_only_private_merkle;
#[path = "../../../crates/aspis-core/src/v7_merkle208.rs"] mod v7_merkle208;
use v7_merkle208::{private_leaf_hash_v7, verify_two_minimal_subtrees_v7_bytes, V7_C1_TREE_TAG};
#[derive(Debug)] pub enum Error { Canonical, Shape, Length, Authentication }
#[path = "ExtractionAuthenticatedC1.rs"] mod authenticated_c1;
#[path = "ExtractionRecordedC1.rs"] mod access;
use access::{RecordedQuery, Digest, Limits, AccessError, extract_first_256, truncated};

thread_local! {
    static REPLAY: RefCell<(BTreeMap<Vec<u8>, [u8; 32]>, usize)> = RefCell::new((BTreeMap::new(), 0));
}
fn hash(parts: &[&[u8]]) -> [u8; 32] {
    REPLAY.with(|slot| {
        let mut replay = slot.borrow_mut();
        let answer = *replay.0.get(&parts.concat()).expect("forbidden new oracle input");
        replay.1 += 1;
        answer
    })
}
fn reset_replay(records: &[RecordedQuery]) {
    REPLAY.with(|slot| *slot.borrow_mut() = (records.iter().map(|r| (r.input.clone(), r.answer)).collect(), 0));
}
fn calls() -> usize { REPLAY.with(|slot| slot.borrow().1) }

struct Fixture { records: Vec<RecordedQuery>, expected: Vec<Vec<M31>> }
impl Fixture {
    fn put(&mut self, input: Vec<u8>) -> Digest {
        let mut answer = [0u8; 32];
        answer[..8].copy_from_slice(&((self.records.len() + 1) as u64).to_le_bytes());
        answer[26..].fill(0xa5);
        let digest = truncated(&answer);
        self.records.push(RecordedQuery { input, answer });
        digest
    }
    fn node(&mut self, left: Digest, right: Digest) -> Digest {
        let mut input = vec![0x11]; input.extend(left); input.extend(right); self.put(input)
    }
    fn subtree(&mut self, height: usize) -> Digest {
        if height == 0 {
            let fibre = self.expected[0].len() / 4;
            let mut value = vec![0u8; 403];
            for slot in 0..4 { for col in 0..26 {
                let v = M31((1 + 100_000 * col + 4 * fibre + slot) as u32);
                authenticated_c1::put31(&mut value, 31 * (slot * 26 + col), v);
                if col < 16 { self.expected[col].push(v); }
            }}
            let mut input = vec![0x10, 0x71]; input.extend(value);
            let mut salt = [0u8; 32]; salt[..8].copy_from_slice(&(fibre as u64).to_le_bytes());
            input.extend(salt); self.put(input)
        } else {
            let left = self.subtree(height - 1); let right = self.subtree(height - 1);
            self.node(left, right)
        }
    }
}
fn limit(records: &[RecordedQuery]) -> Limits {
    Limits { records: records.len(), raw_bytes: records.iter().map(|r| r.input.len()).sum(), lookups: 521 }
}
fn failed(records: &[RecordedQuery], root: Digest, limits: Limits, expected: AccessError) {
    match extract_first_256(records, root, limits) {
        Err(actual) => assert_eq!(actual, expected),
        Ok(_) => panic!("expected access failure {expected:?}"),
    }
}
fn main() {
    let mut fixture = Fixture { records: Vec::new(), expected: vec![Vec::new(); 16] };
    let mut root = fixture.subtree(8);
    let mut expected_frontier = Vec::new();
    for height in 8..18 {
        // These off-path sibling digests have NO preimages in the prefix.
        let mut sibling = [0xff; 26]; sibling[0] = height as u8;
        expected_frontier.extend(sibling); root = fixture.node(root, sibling);
    }
    assert_eq!(fixture.records.len(), 521);
    reset_replay(&fixture.records);
    let material = extract_first_256(&fixture.records, root, limit(&fixture.records)).unwrap();
    assert_eq!(calls(), 0, "the access stage has no oracle-query capability");
    assert_eq!((material.stats.lookups, material.stats.leaves, material.stats.parents,
        material.stats.frontier_digests), (521, 256, 265, 10));
    assert_eq!(material.openings.frontier, expected_frontier);
    assert_eq!(material.openings.ids, (0..256).collect::<Vec<_>>());
    let values = authenticated_c1::authenticate(root, &material.openings).unwrap();
    assert_eq!(values, fixture.expected, "same slot-major 26-column packing, semantic16 projection");
    assert_eq!(calls(), 786, "256 leaves plus twice 265 parents, all cached");
    assert_eq!(256 * (403 + 32) + material.openings.frontier.len(), 111_620);

    let mut failures = 0;
    let mut check = |log: &[RecordedQuery], lim: Limits, expected| {
        failed(log, root, lim, expected); failures += 1;
    };
    let mut smaller = limit(&fixture.records); smaller.records -= 1;
    check(&fixture.records, smaller, AccessError::QueryBudget);
    let mut smaller = limit(&fixture.records); smaller.raw_bytes -= 1;
    check(&fixture.records, smaller, AccessError::ByteBudget);
    let mut smaller = limit(&fixture.records); smaller.lookups = 520;
    check(&fixture.records, smaller, AccessError::LookupBudget);
    check(&fixture.records[..520], limit(&fixture.records[..520]), AccessError::MissingRoot);
    check(&fixture.records[1..], limit(&fixture.records[1..]), AccessError::MissingPreimage);
    let mut changed = fixture.records.clone(); let last = changed.pop().unwrap(); changed.insert(0, last);
    check(&changed, limit(&changed), AccessError::ForwardReference);
    let mut changed = fixture.records.clone(); changed[0].input[1] = 0xf1;
    check(&changed, limit(&changed), AccessError::MalformedLeaf);
    let mut changed = fixture.records.clone(); changed[0].input.pop();
    check(&changed, limit(&changed), AccessError::MalformedLeaf);
    let mut changed = fixture.records.clone(); changed.last_mut().unwrap().input[0] = 0x10;
    check(&changed, limit(&changed), AccessError::MalformedNode);
    let mut changed = fixture.records.clone(); changed.last_mut().unwrap().input.pop();
    check(&changed, limit(&changed), AccessError::MalformedNode);
    let mut changed = fixture.records.clone(); changed[0].input[2..5].fill(255); changed[0].input[5] |= 127;
    check(&changed, limit(&changed), AccessError::NoncanonicalLeaf);
    let mut changed = fixture.records.clone(); let mut repeated = changed[0].clone(); repeated.answer[31] ^= 1; changed.push(repeated);
    check(&changed, limit(&changed), AccessError::InconsistentAnswer);
    let mut changed = fixture.records.clone(); let mut colliding = changed[0].clone(); colliding.input.push(9); changed.push(colliding);
    check(&changed, limit(&changed), AccessError::TruncatedCollision);
    let mut changed = fixture.records.clone(); let mut colliding = changed[0].clone(); colliding.input.push(9); colliding.answer[31] ^= 1; changed.push(colliding);
    check(&changed, limit(&changed), AccessError::TruncatedCollision);
    // Missing-prefix material cannot be manufactured by appending the missing
    // preimage after its already-recorded parent. It remains a forward edge.
    let mut changed = fixture.records[1..].to_vec(); changed.push(fixture.records[0].clone());
    check(&changed, limit(&changed), AccessError::ForwardReference);
    assert_eq!(failures, 15);
    let mut repeated = fixture.records.clone(); repeated.extend(fixture.records.clone());
    let same = extract_first_256(&repeated, root, limit(&repeated)).unwrap();
    assert_eq!(same.stats.unique_inputs, 521);
    assert_eq!(same.openings.frontier, material.openings.frontier);
    assert_eq!(same.openings.leaves, material.openings.leaves);
    assert_eq!(calls(), 786, "none of the access controls queried an oracle");
    println!("PASS extraction_access records=521 lookups=521 leaves=256 parents=265 frontier=10 bytes=111620 new_oracle_calls=0 cached_auth_calls=786 scalar_values=16384");
    println!("PASS failure_controls=15 repeat_control=1 missing_off_path_preimages=10 accepted=true");
    println!("SCOPE source authenticate and Merkle loop reused; consistent synthetic recorded answers, not SHA/ROM sampling. No coefficients, witness, successful selected proof, or validator completeness claimed.");
}
