//! Read-only, first-q22-cut input-address audit. No hash answer is changed.
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Mutex, OnceLock};

#[derive(Default)]
struct Audit {
    lengths: BTreeMap<usize, usize>,
    seen33: BTreeSet<Vec<u8>>,
    seen42: BTreeSet<Vec<u8>>,
    nonce_calls: usize,
    last_nonce_fresh: bool,
    started: bool,
    finished: bool,
    query_calls: Vec<(Vec<u8>, bool)>,
    query_other: usize,
}

fn audit() -> Option<&'static Mutex<Audit>> {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    static AUDIT: OnceLock<Mutex<Audit>> = OnceLock::new();
    if *ENABLED.get_or_init(|| std::env::var_os("ASPIS_R15_QUERY_AUDIT").is_some()) {
        Some(AUDIT.get_or_init(|| Mutex::new(Audit::default())))
    } else {
        None
    }
}

pub fn observe(parts: &[&[u8]]) {
    let Some(shared) = audit() else { return };
    let mut a = shared.lock().unwrap();
    if a.finished {
        return;
    }
    let len = parts.iter().map(|p| p.len()).sum();
    *a.lengths.entry(len).or_default() += 1;
    if len == 33 {
        let input = parts.concat();
        let fresh = a.seen33.insert(input.clone());
        if a.started {
            a.query_calls.push((input, fresh));
        }
    } else {
        if a.started {
            a.query_other += 1;
        }
        if len == 42 {
            let input = parts.concat();
            let fresh = a.seen42.insert(input.clone());
            if input[32] == 0 && input[33] == 5 {
                a.nonce_calls += 1;
                a.last_nonce_fresh = fresh;
            }
        }
    }
}

pub fn begin(state: [u8; 32]) {
    let Some(shared) = audit() else { return };
    let mut a = shared.lock().unwrap();
    if a.started {
        return;
    }
    let output_key = [&state[..], &[1]].concat();
    let advance_key = [&state[..], &[2]].concat();
    eprintln!("R15_FIRST_QUERY_AUDIT lengths={:?} unique33={} nonce_calls={} nonce_fresh={} output_fresh={} advance_fresh={}",
        a.lengths, a.seen33.len(), a.nonce_calls, a.last_nonce_fresh,
        !a.seen33.contains(&output_key), !a.seen33.contains(&advance_key));
    a.started = true;
}

pub fn end() {
    let Some(shared) = audit() else { return };
    let mut a = shared.lock().unwrap();
    if !a.started || a.finished {
        return;
    }
    let paired = a.query_calls.len() % 2 == 0
        && a.query_calls
            .chunks_exact(2)
            .all(|p| p[0].0[32] == 1 && p[1].0[32] == 2 && p[0].0[..32] == p[1].0[..32]);
    eprintln!(
        "R15_QUERY_BLOCK_AUDIT calls33={} all_fresh={} same_old_state_pairs={} other_calls={}",
        a.query_calls.len(),
        a.query_calls.iter().all(|(_, fresh)| *fresh),
        paired,
        a.query_other
    );
    a.finished = true;
}
