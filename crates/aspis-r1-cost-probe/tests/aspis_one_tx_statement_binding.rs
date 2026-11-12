//! Aspis one-transaction verifier: a proof is bound to its public statement.
//!
//! For each of the six saved fixtures the proof is re-packed into the
//! one-transaction format and must verify against its own statement. Then one
//! field of the statement is changed at a time and the same proof is offered
//! again. Every field that reaches the transcript through `public_bytes` must
//! make the verifier reject: payment data (nullifier, commitments, amount,
//! anchor root), the lane transition, and the binding tail added at the PIN2
//! pin (pool, deployment domain, withdrawal destination).
//!
//! Two fields of the statement do not reach the transcript in the pinned
//! design and so do not here either: the source sequence number and the source
//! current root (see the comment on `public_bytes`). The second test records
//! how the verifier treats each: the sequence number is rejected by a guard,
//! the current root is not bound by the proof at all.
//!
//! Run: cargo test --release -p aspis-r1-cost-probe --features prover --test aspis_one_tx_statement_binding

use aspis_core::field::M31;
use aspis_core::Digest32;
use aspis_r1_cost_probe::verifier::candidate::one_tx::{pack, verify};
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_terminal_statement_v1, PoolV1PairForestTerminalStatementV1 as Statement,
};
use sha2::{Digest, Sha256};

#[derive(Clone, Copy)]
struct Sha;
impl Digest32 for Sha {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
        let mut d = Sha256::new();
        for part in parts {
            d.update(part);
        }
        d.finalize().into()
    }
}

macro_rules! fixture {
    ($name:literal) => {
        (
            $name,
            include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/", $name, "/r1-s2-proof.bin")) as &[u8],
            include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/", $name, "/r1-s2-public-asf8.bin")) as &[u8],
        )
    };
}
const FIXTURES: [(&str, &[u8], &[u8]); 6] = [
    fixture!("transfer-13"),
    fixture!("transfer-255"),
    fixture!("transfer-1023"),
    fixture!("withdrawal-13"),
    fixture!("withdrawal-255"),
    fixture!("withdrawal-1023"),
];

/// A different canonical field element.
fn nudge(x: &mut M31) {
    x.0 = if x.0 == 0 { 1 } else { x.0 - 1 };
}

type Change = (&'static str, fn(&mut Statement) -> bool);

/// Changes to fields that `public_bytes` serializes. A change returns false when it does not apply to the variant.
const BOUND: &[Change] = &[
    ("pool", |s| { match s { Statement::PrivateTransfer { public, .. } => public.pool[0] ^= 1, Statement::Withdrawal { public, .. } => public.pool[0] ^= 1 } true }),
    ("deployment domain", |s| { match s { Statement::PrivateTransfer { public, .. } => public.deployment_domain[31] ^= 0x80, Statement::Withdrawal { public, .. } => public.deployment_domain[31] ^= 0x80 } true }),
    ("withdrawal destination", |s| match s { Statement::Withdrawal { public, .. } => { public.destination_token_account[7] ^= 1; true } _ => false }),
    ("withdrawal amount", |s| match s { Statement::Withdrawal { public, .. } => { public.amount += 1; true } _ => false }),
    ("recipient commitment", |s| match s { Statement::PrivateTransfer { public, .. } => { nudge(&mut public.recipient_commitment[0]); true } _ => false }),
    ("change commitment", |s| { match s { Statement::PrivateTransfer { public, .. } => nudge(&mut public.change_commitment[3]), Statement::Withdrawal { public, .. } => nudge(&mut public.change_commitment[3]) } true }),
    ("nullifier", |s| { match s { Statement::PrivateTransfer { public, .. } => nudge(&mut public.nullifier[0]), Statement::Withdrawal { public, .. } => nudge(&mut public.nullifier[0]) } true }),
    ("anchor root", |s| { match s { Statement::PrivateTransfer { public, .. } => nudge(&mut public.anchor_root[1]), Statement::Withdrawal { public, .. } => nudge(&mut public.anchor_root[1]) } true }),
    ("asset id", |s| { match s { Statement::PrivateTransfer { public, .. } => nudge(&mut public.asset_id), Statement::Withdrawal { public, .. } => nudge(&mut public.asset_id) } true }),
    ("source next pair index", |s| { match s { Statement::PrivateTransfer { common, .. } | Statement::Withdrawal { common, .. } => common.lane_transition.live_snapshot.next_pair_index += 1 } true }),
    ("source frontier", |s| { match s { Statement::PrivateTransfer { common, .. } | Statement::Withdrawal { common, .. } => nudge(&mut common.lane_transition.live_snapshot.frontier[0][0]) } true }),
    ("afterstate root", |s| { match s { Statement::PrivateTransfer { common, .. } | Statement::Withdrawal { common, .. } => nudge(&mut common.lane_transition.candidate_afterstate.next_root[0]) } true }),
    ("afterstate frontier", |s| { match s { Statement::PrivateTransfer { common, .. } | Statement::Withdrawal { common, .. } => nudge(&mut common.lane_transition.candidate_afterstate.next_frontier[19][7]) } true }),
];

/// Statement fields that the pinned `public_bytes` does not serialize.
const NOT_IN_TRANSCRIPT: &[Change] = &[
    ("source sequence number", |s| { match s { Statement::PrivateTransfer { common, .. } | Statement::Withdrawal { common, .. } => common.lane_transition.live_snapshot.sequence += 1 } true }),
    ("source current root", |s| { match s { Statement::PrivateTransfer { common, .. } | Statement::Withdrawal { common, .. } => nudge(&mut common.lane_transition.live_snapshot.current_root[0]) } true }),
];

fn packed(name: &str, proof: &[u8], statement: &Statement) -> Vec<u8> {
    let packed = pack(statement.semantic_public(), proof, Sha).unwrap_or_else(|e| panic!("{name}: re-pack {e:?}"));
    verify(statement.semantic_public(), &packed, Sha, None).unwrap_or_else(|e| panic!("{name}: own statement {e:?}"));
    packed
}

#[test]
fn a_proof_is_rejected_against_a_statement_changed_in_any_transcript_field() {
    let mut checked = 0;
    for (name, proof, public) in FIXTURES {
        let statement = decode_pool_v1_pair_forest_terminal_statement_v1(public).unwrap();
        let packed = packed(name, proof, &statement);
        for (field, change) in BOUND {
            let mut other = statement.clone();
            if !change(&mut other) {
                continue;
            }
            assert!(other != statement, "{name}: {field} change did not change the statement");
            assert!(
                verify(other.semantic_public(), &packed, Sha, None).is_err(),
                "{name}: the proof was ACCEPTED against a statement with a different {field}"
            );
            checked += 1;
        }
    }
    // 3 transfers x 11 applicable changes + 3 withdrawals x 12.
    assert_eq!(checked, 3 * 11 + 3 * 12);
}

#[test]
fn the_two_source_fields_outside_the_transcript_bytes_behave_as_recorded() {
    // Neither field is serialized by `public_bytes`, so neither reaches the transcript.
    //   * source sequence number: a change is still rejected, by the guard that requires it to
    //     equal the next pair index (which is in the transcript);
    //   * source current root: a change is ACCEPTED by this function. The proof does not bind it.
    //     The one-transaction entry does not take the statement from the prover: it reconstructs
    //     it from the request and the authenticated lane account. This test records the fact so
    //     that nobody relies on the proof for that field.
    for (name, proof, public) in FIXTURES {
        let statement = decode_pool_v1_pair_forest_terminal_statement_v1(public).unwrap();
        let packed = packed(name, proof, &statement);
        for (field, change) in NOT_IN_TRANSCRIPT {
            let mut other = statement.clone();
            assert!(change(&mut other) && other != statement);
            assert_eq!(
                other.semantic_public().public_bytes().unwrap(),
                statement.semantic_public().public_bytes().unwrap(),
                "{name}: {field} now reaches the transcript; move it to the bound list"
            );
            let verdict = verify(other.semantic_public(), &packed, Sha, None);
            match *field {
                "source sequence number" => assert!(verdict.is_err(), "{name}: {field} is no longer guarded"),
                "source current root" => assert!(verdict.is_ok(), "{name}: {field} is now rejected; update this record"),
                _ => unreachable!(),
            }
        }
    }
}
