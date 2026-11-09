//! R14 source Transcript KAT. Research-only deterministic public data.
//! Does NOT prove a random-oracle law or instantiate a full q22 prover.
#![cfg(feature = "insecure-spend-fixture")]
use aspis_core::{
    field::QM31,
    state_only_hiding::begin_state_only_masked_sumcheck,
    transcript::{label, Transcript},
};
use sha2::{Digest, Sha256};
use std::cell::RefCell;
thread_local! {static CALLS:RefCell<Vec<Vec<u8>>>=RefCell::new(Vec::new());}
fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let bytes = parts.concat();
    CALLS.with(|c| c.borrow_mut().push(bytes.clone()));
    Sha256::digest(bytes).into()
}
fn read_q(bytes: &[u8], cursor: &mut usize) -> QM31 {
    let end = cursor.checked_add(16).expect("cursor overflow");
    let q =
        QM31::from_le_bytes(bytes.get(*cursor..end).expect("short KAT")).expect("noncanonical KAT");
    *cursor = end;
    q
}
#[test]
fn r14_literal_initial_eta_and_three_compact_rounds_match_python() {
    let data = include_bytes!("support/r14_public_prefix.bin");
    assert_eq!(&data[..8], b"R14PUB01");
    let root = &data[8..34];
    let mut cursor = 34;
    let view: Vec<_> = (0..82).map(|_| read_q(data, &mut cursor)).collect();
    let eta_expected = read_q(data, &mut cursor);
    let challenges: Vec<_> = (0..3).map(|_| read_q(data, &mut cursor)).collect();
    let final_state: [u8; 32] = data[cursor..cursor + 32].try_into().unwrap();
    cursor += 32;
    assert_eq!(cursor, data.len());
    CALLS.with(|c| c.borrow_mut().clear());
    let mut t = Transcript::new(hash);
    let entry = [&b"R14-public-post-C2-entry-v1"[..], root].concat();
    t.absorb(label::STATEMENT, &entry);
    assert_eq!(
        begin_state_only_masked_sumcheck(&mut t, view[0]).unwrap(),
        eta_expected
    );
    for round in 0..3 {
        let mut framed = [0u8; 433];
        framed[0] = round as u8;
        for (sent, q) in view[1 + 27 * round..28 + 27 * round].iter().enumerate() {
            q.write_le_bytes(&mut framed[1 + 16 * sent..17 + 16 * sent]);
        }
        t.absorb(label::V6_COMPACT_SEMANTIC_ROUND, &framed);
        assert_eq!(t.challenge_qm31().unwrap(), challenges[round]);
    }
    assert_eq!(t.diagnostic_state(), final_state);
    CALLS.with(|calls| {
        let calls = calls.borrow();
        assert_eq!(calls.len(), 13);
        // Pin every full input and full 32-byte answer, including discarded
        // challenge bits; checking only returned field elements is weaker.
        let mut all = Sha256::new();
        for key in calls.iter() {
            all.update((key.len() as u32).to_le_bytes());
            all.update(key);
            all.update(Sha256::digest(key));
        }
        let got: [u8; 32] = all.finalize().into();
        assert_eq!(
            got,
            [
                101, 242, 188, 163, 231, 79, 147, 129, 122, 150, 7, 137, 221, 193, 69, 217, 38, 91,
                176, 103, 20, 145, 23, 83, 162, 99, 125, 1, 13, 218, 179, 230
            ]
        );
        assert_eq!(calls[1].len(), 52);
        assert_eq!(&calls[1][32..36], &[0, 31, 27, 10]);
        for start in [4usize, 7, 10] {
            assert_eq!(calls[start].len(), 467);
            assert_eq!(calls[start][33], 48);
            assert_eq!(calls[start + 1].len(), 33);
            assert_eq!(calls[start + 2].len(), 33);
        }
    });
}
