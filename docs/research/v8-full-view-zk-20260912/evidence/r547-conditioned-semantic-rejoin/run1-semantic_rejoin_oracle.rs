use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

#[derive(Default)]
struct State {
    memo: HashMap<Vec<u8>, [u8; 32]>,
    programmed: Option<Vec<u8>>,
    armed: bool,
    first_read: bool,
    program_entries: usize,
    programmed_reads: usize,
    prover_reads: usize,
    verifier_replay_reads: usize,
    other_replay_reads: usize,
    phase: u8,
    total_calls: usize,
    memo_hits: usize,
}

static ORACLE: OnceLock<Mutex<State>> = OnceLock::new();

fn state() -> &'static Mutex<State> {
    ORACLE.get_or_init(|| Mutex::new(State::default()))
}

pub fn hash(parts: &[&[u8]]) -> [u8; 32] {
    // HashFn consumes the concatenated byte string, so memoize that exact
    // preimage independent of how its caller partitions the slices.
    let key: Vec<u8> = parts.iter().flat_map(|part| part.iter().copied()).collect();
    let mut state = state().lock().unwrap();
    state.total_calls += 1;
    if let Some(value) = state.memo.get(&key).copied() {
        state.memo_hits += 1;
        if state.programmed.as_ref() == Some(&key) {
            state.programmed_reads += 1;
            if !state.first_read {
                state.first_read = true;
                state.prover_reads += 1;
            } else if state.phase == 1 {
                state.verifier_replay_reads += 1;
            } else {
                state.other_replay_reads += 1;
            }
        }
        return value;
    }

    let mut sha = Sha256::new();
    sha.update(&key);
    let value: [u8; 32] = sha.finalize().into();
    state.memo.insert(key, value);
    value
}

pub fn program_next_squeeze(state_bytes: [u8; 32]) {
    let mut key = state_bytes.to_vec();
    key.push(0x01); // selected transcript's DOM_SQUEEZE byte
    let mut state = state().lock().unwrap();
    assert!(!state.armed, "only one programmed oracle entry is permitted");
    assert!(
        !state.memo.contains_key(&key),
        "programmed preimage was read before arming"
    );
    // Install one immutable entry before its first read. Prover and all
    // verifier executions then share this exact cached output.
    state.memo.insert(key.clone(), [0; 32]);
    state.programmed = Some(key.clone());
    state.armed = true;
    state.program_entries += 1;
    if let Ok(directory) = std::env::var("ASPIS_SEMANTIC_REJOIN_OUTPUT") {
        let mut entry = key.clone();
        entry.extend_from_slice(&[0u8; 32]);
        std::fs::write(format!("{directory}/programmed-entry.bin"), &entry)
            .expect("write the exact programmed preimage and output");
        let key_digest: [u8; 32] = Sha256::digest(&key).into();
        println!("PROGRAMMED_ORACLE_ENTRY bytes={} key_sha256={:02x?} output_bytes=32 output=zero32", key.len(), key_digest);
    }
}

pub fn set_phase(phase: u8) {
    state().lock().unwrap().phase = phase;
}

pub fn report() {
    let state = state().lock().unwrap();
    println!(
        "PROGRAMMED_ORACLE_COUNTS entries={} programmed_reads={} prover_reads={} selected_verifier_replay_reads={} other_replays={} memo_entries={} memo_hits={} total_hash_calls={} programmed_output=all_zero",
        state.program_entries,
        state.programmed_reads,
        state.prover_reads,
        state.verifier_replay_reads,
        state.other_replay_reads,
        state.memo.len(),
        state.memo_hits,
        state.total_calls
    );
    assert!(state.armed, "programmed challenge was never armed");
    assert!(state.first_read, "programmed challenge was never read by prover");
    assert_eq!(state.program_entries, 1, "exactly one programmed entry required");
    assert_eq!(state.prover_reads, 1, "programmed challenge must be read once by prover");
    assert_eq!(
        state.verifier_replay_reads, 2,
        "two selected verifier invocations must reuse the cached entry"
    );
    assert_eq!(
        state.memo.get(state.programmed.as_ref().unwrap()),
        Some(&[0u8; 32])
    );
}
