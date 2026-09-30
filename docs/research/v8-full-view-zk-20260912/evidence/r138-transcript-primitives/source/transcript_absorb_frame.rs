//! Extraction-only R137 probe: record the hash input supplied by Transcript::absorb.
//! This test does not touch production source paths or add a hash dependency.

use aspis_core::transcript::{HashFn, Transcript};
use std::cell::RefCell;

thread_local! {
    static INPUTS: RefCell<Vec<Vec<u8>>> = const { RefCell::new(Vec::new()) };
    static SHAPES: RefCell<Vec<Vec<usize>>> = const { RefCell::new(Vec::new()) };
}

fn recording_hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut joined = Vec::new();
    for part in parts {
        joined.extend_from_slice(part);
    }
    INPUTS.with(|inputs| inputs.borrow_mut().push(joined));
    SHAPES.with(|shapes| {
        shapes
            .borrow_mut()
            .push(parts.iter().map(|part| part.len()).collect())
    });
    [0u8; 32]
}

fn take_inputs() -> Vec<Vec<u8>> {
    INPUTS.with(|inputs| std::mem::take(&mut *inputs.borrow_mut()))
}

fn take_shapes() -> Vec<Vec<usize>> {
    SHAPES.with(|shapes| std::mem::take(&mut *shapes.borrow_mut()))
}

fn expected(label: u8, data: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; 32];
    out.extend_from_slice(&[0, label]);
    out.extend_from_slice(data);
    out
}

fn assert_absorb_frame(hash: HashFn, label: u8, data: &[u8]) {
    let mut transcript = Transcript::new(hash);
    transcript.absorb(label, data);
    let inputs = take_inputs();
    assert_eq!(inputs, vec![expected(label, data)]);
}

fn assert_absorb_shape(label: u8, payload_len: usize, packed: bool) {
    let data = vec![0xa5u8; payload_len];
    let mut transcript = Transcript::new(recording_hash);
    transcript.absorb(label, &data);
    let shapes = take_shapes();
    let shape_expected = if packed {
        vec![vec![34 + payload_len]]
    } else {
        vec![vec![32, 2, payload_len]]
    };
    assert_eq!(shapes, shape_expected, "payload length {payload_len}");
    assert_eq!(take_inputs(), vec![expected(label, &data)]);
}

#[test]
fn absorb_short_record_is_state_frame_label_data() {
    assert_absorb_frame(recording_hash, 0x2a, b"short-r137");
}

#[test]
fn absorb_long_record_is_state_frame_label_data() {
    let data = vec![0x5bu8; 159];
    assert_absorb_frame(recording_hash, 0x37, &data);
}

/// Extraction-only schedule evidence for the pinned
/// `experiments/relation_callback.rs` absorb sites. The labels are represented
/// by stable test bytes because this probe deliberately does not import or
/// modify the production callback. `Transcript::absorb` itself determines the
/// packed/long branch from the payload length.
#[test]
fn pinned_relation_callback_absorb_payload_shapes() {
    // relation-callback prefix: profile, statement, roots, point claims,
    // OOD vectors, payment nonce, inactive claim.
    let cases = [
        ("callback profile", 24, true),
        ("statement", 32, true),
        ("root", 26, true),
        ("second-phase root", 26, true),
        ("point claims", 358 * 16, false),
        ("OOD vector 1", 1 + 29 * 16, false),
        ("OOD vector 2", 1 + 29 * 16, false),
        ("payment nonce", 8, true),
        ("inactive claim", 16, true),
        ("ordinary profile", 1024 * 16, false),
        ("claim", 16, true),
        ("image profile", 22, true),
        ("final256", 256 * 16, false),
        ("grind nonce", 8, true),
        ("query profile", 18, true),
        ("compact relation round", 1 + 6 * 16, true),
        ("circle-fold nonce", 1 + 8, true),
    ];

    for (index, &(_name, payload_len, packed)) in cases.iter().enumerate() {
        assert_absorb_shape(index as u8, payload_len, packed);
    }
}

#[test]
fn pinned_relation_callback_round_absorb_occurs_four_times() {
    for round in 0..4u8 {
        assert_absorb_shape(round, 1 + 6 * 16, true);
    }
}
