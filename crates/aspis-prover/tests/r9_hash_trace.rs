//! Research-only, in-memory trace of the pinned source salt/leaf prefix.
//! This is a base V7 helper instantiation, not the unavailable generated q22
//! producer and not a universal call-graph or query-cap certificate.

use std::cell::RefCell;

use aspis_core::state_only_hiding::StateOnlyHidingContext;
use aspis_core::v7_merkle208::{private_leaf_hash_v7, V7_C1_TREE_TAG, V7_C2_TREE_TAG};
use aspis_prover::state_only_entropy::StateOnlyAttemptSecrets;
use aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore;
use sha2::{Digest, Sha256};
use zeroize::Zeroize;

type HashFn = fn(&[&[u8]]) -> [u8; 32];

struct HashEvent {
    phase: u32,
    input: Vec<u8>,
    answer: [u8; 32],
}

impl Drop for HashEvent {
    fn drop(&mut self) {
        self.input.zeroize();
        self.answer.zeroize();
    }
}

struct Capture {
    events: Vec<HashEvent>,
    total_calls: u64,
    truncated: bool,
    stored_bytes: usize,
    max_bytes: usize,
    max_events: usize,
    phase: u32,
}

impl Capture {
    fn complete(&self) -> bool {
        !self.truncated && self.total_calls == self.events.len() as u64
    }
}

struct Session {
    backend: HashFn,
    capture: Capture,
}

thread_local! {
    static SESSION: RefCell<Option<Session>> = const { RefCell::new(None) };
}

struct ClearOnDrop;

impl Drop for ClearOnDrop {
    fn drop(&mut self) {
        SESSION.with(|cell| {
            cell.borrow_mut().take();
        });
    }
}

fn capture<T>(
    backend: HashFn,
    max_bytes: usize,
    max_events: usize,
    run: impl FnOnce(HashFn) -> T,
) -> (T, Capture) {
    SESSION.with(|cell| {
        assert!(cell.borrow().is_none(), "nested capture unsupported");
        *cell.borrow_mut() = Some(Session {
            backend,
            capture: Capture {
                events: Vec::new(),
                total_calls: 0,
                truncated: false,
                stored_bytes: 0,
                max_bytes,
                max_events,
                phase: 0,
            },
        });
    });
    let _cleanup = ClearOnDrop;
    let output = run(recording_hash);
    let session = SESSION.with(|cell| cell.borrow_mut().take().expect("active capture"));
    (output, session.capture)
}

fn phase(id: u32) {
    SESSION.with(|cell| {
        cell.borrow_mut()
            .as_mut()
            .expect("active capture")
            .capture
            .phase = id;
    });
}

fn recording_hash(parts: &[&[u8]]) -> [u8; 32] {
    let backend = SESSION.with(|cell| cell.borrow().as_ref().expect("capture thread").backend);
    let answer = backend(parts);
    SESSION.with(|cell| {
        let mut session = cell.borrow_mut();
        let capture = &mut session.as_mut().expect("active capture").capture;
        capture.total_calls = capture.total_calls.saturating_add(1);
        let Some(input_len) = parts
            .iter()
            .try_fold(0usize, |n, part| n.checked_add(part.len()))
        else {
            capture.truncated = true;
            return;
        };
        let cost = input_len.checked_add(32);
        if capture.events.len() >= capture.max_events
            || cost
                .and_then(|value| capture.stored_bytes.checked_add(value))
                .is_none_or(|value| value > capture.max_bytes)
        {
            capture.truncated = true;
            return;
        }
        let mut input = Vec::with_capacity(input_len);
        for part in parts {
            input.extend_from_slice(part);
        }
        capture.stored_bytes += cost.expect("checked above");
        capture.events.push(HashEvent {
            phase: capture.phase,
            input,
            answer,
        });
    });
    answer
}

fn sha256(parts: &[&[u8]]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize().into()
}

#[test]
fn pinned_pool_helper_retains_salt_through_typed_c2_leaf() {
    const PHASE_RESERVE: u32 = 1;
    const PHASE_C1: u32 = 2;
    const PHASE_C2: u32 = 3;
    let ((salt, other, c1_digest, c2_digest), trace) =
        capture(sha256, 4 * 1024 * 1024, 20_000, |hash| {
            phase(PHASE_RESERVE);
            let nonce = [0x23; 32];
            let context = StateOnlyHidingContext::pool_v1_pair_forest_v1([0x45; 32], nonce);
            let attempt =
                StateOnlyAttemptSecrets::deterministic_spend_fixture(nonce, [0x67; 32], [0x89; 32]);
            let mut nonces = InMemoryStateOnlyMaskNonceStore::default();
            let (reserved, _material) = attempt
                .reserve_and_build_pool_v1_pair_forest_mask_material_v1(
                    hash,
                    [0xab; 32],
                    context,
                    &mut nonces,
                )
                .expect("pinned source reservation");

            phase(PHASE_C1);
            let salt = reserved
                .derive_pool_v1_leaf_salt(hash, context, 0x77, 7)
                .expect("C1 salt");
            let c1_digest = private_leaf_hash_v7(hash, V7_C1_TREE_TAG, &[0x11; 403], &salt);

            phase(PHASE_C2);
            // The selected generated prefix retains `salts[i]` from the C1
            // loop and passes that same value into the C2 typed leaf.
            let c2_digest = private_leaf_hash_v7(hash, V7_C2_TREE_TAG, &[0x22; 186], &salt);
            let other = reserved
                .derive_pool_v1_leaf_salt(hash, context, 0x77, 8)
                .expect("next logical address");
            (salt, other, c1_digest, c2_digest)
        });

    assert!(trace.complete());
    assert_ne!(salt, other);
    assert_eq!(c1_digest.len(), 26);
    assert_eq!(c2_digest.len(), 26);

    let c1_leaf = trace
        .events
        .iter()
        .find(|event| {
            event.phase == PHASE_C1
                && event.input.len() == 437
                && event.input.starts_with(&[0x10, V7_C1_TREE_TAG])
        })
        .expect("complete C1 typed-leaf call");
    let c2_leaf = trace
        .events
        .iter()
        .find(|event| {
            event.phase == PHASE_C2
                && event.input.len() == 220
                && event.input.starts_with(&[0x10, V7_C2_TREE_TAG])
        })
        .expect("complete C2 typed-leaf call");
    assert_eq!(&c1_leaf.input[c1_leaf.input.len() - 32..], salt);
    assert_eq!(&c2_leaf.input[c2_leaf.input.len() - 32..], salt);

    let address7_derivations: Vec<_> = trace
        .events
        .iter()
        .filter(|event| {
            event
                .input
                .starts_with(b"aspis:state-only:private-leaf-salt:v1")
                && event.input.ends_with(&[0x89; 32])
                && event.input[event.input.len() - 37] == 0x77
                && &event.input[event.input.len() - 36..event.input.len() - 32]
                    == 7u32.to_le_bytes().as_slice()
        })
        .collect();
    assert_eq!(address7_derivations.len(), 1);
    assert_eq!(address7_derivations[0].answer, salt);
    let salt_derivation_calls = trace
        .events
        .iter()
        .filter(|event| {
            event
                .input
                .starts_with(b"aspis:state-only:private-leaf-salt:v1")
        })
        .count();
    assert_eq!(salt_derivation_calls, 2);
    eprintln!(
        "R9_SELECTED_HELPER_PREFIX complete=true total_calls={} salt_derivations={} address7_calls={} retained_salt_leaf_uses=2 typed_c1=1 typed_c2=1",
        trace.total_calls,
        salt_derivation_calls,
        address7_derivations.len(),
    );
}
