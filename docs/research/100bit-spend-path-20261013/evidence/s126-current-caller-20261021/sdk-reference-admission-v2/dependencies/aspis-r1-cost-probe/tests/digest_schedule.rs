//! Concrete SHA-256 call-shape regression; no arbitrary-backend equivalence claim.
#![cfg(feature = "prover")]
use aspis_core::Digest32;
use aspis_r1_cost_probe::{
    r1_wire::{self, SemanticTranscript},
    transcript::Transcript,
    transport::Variant,
};
use sha2::{Digest, Sha256};
use std::cell::RefCell;

type Call = (Vec<Vec<u8>>, [u8; 32]);
thread_local! { static CALLS: RefCell<Vec<Call>> = const { RefCell::new(Vec::new()) }; }
#[derive(Clone, Copy)]
struct TracedSha256;
fn sha(parts: &[&[u8]]) -> [u8; 32] {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update(part);
    }
    digest.finalize().into()
}
impl Digest32 for TracedSha256 {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
        let out = sha(parts);
        CALLS.with(|calls| {
            calls
                .borrow_mut()
                .push((parts.iter().map(|p| p.to_vec()).collect(), out))
        });
        out
    }
}
fn take() -> Vec<Call> {
    CALLS.with(|calls| core::mem::take(&mut *calls.borrow_mut()))
}
fn expected(parts: &[&[u8]]) -> Call {
    (parts.iter().map(|p| p.to_vec()).collect(), sha(parts))
}
fn semantic_step(state: [u8; 32], row: u8, record: &[u8]) -> ([u8; 32], Vec<Call>) {
    let absorbed = expected(&[&state, &[0, 0xa0 + row], record]);
    let block = expected(&[&absorbed.1, &[1]]);
    let advance = expected(&[&absorbed.1, &[2]]);
    (advance.1, vec![absorbed, block, advance])
}

#[test]
fn concrete_sha256_constructor_rows_reseed_queries_and_rho_keep_exact_calls() {
    take();
    let public = b"digest32 schedule regression";
    let root = [0x57; 32];
    let init = expected(&[
        r1_wire::DOMAIN,
        &[0],
        &(public.len() as u32).to_le_bytes(),
        public,
        &root,
    ]);
    let mut semantic = SemanticTranscript::new(TracedSha256, public, &root).unwrap();
    assert_eq!(take(), vec![init.clone()]);
    let mut state = init.1;
    for row in 0..27 {
        let record = r1_wire::record(row, &vec![0; r1_wire::row_shape(row).unwrap().1]).unwrap();
        let (next, calls) = semantic_step(state, row, &record);
        if row <= 24 {
            semantic.semantic(row, &record).unwrap();
        } else {
            semantic
                .challenge_reference_circle_point(row, &record)
                .unwrap();
        }
        assert_eq!(take(), calls, "semantic row {row}");
        assert_eq!(semantic.state(), next);
        assert_eq!(semantic.next_row(), row + 1);
        state = next;
    }
    // Row mismatch rejects before hashing and leaves both carried values intact.
    assert!(semantic
        .semantic(0, &r1_wire::record(0, &[]).unwrap())
        .is_err());
    assert!(take().is_empty());
    assert_eq!(semantic.state(), state);
    assert_eq!(semantic.next_row(), 27);
    for variant in [Variant::S1, Variant::S2] {
        #[cfg(not(feature = "private-leaf-salts"))]
        let domain: &[u8] = b"UNPROVED:R1:COST-PROBE:P2";
        #[cfg(feature = "private-leaf-salts")]
        let domain: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:P3";
        let reseed = expected(&[domain, &[variant.tag()], &state]);
        let mut opening = Transcript::new(TracedSha256, state, variant);
        assert_eq!(take(), vec![reseed.clone()]);
        let mut carried = reseed.1;
        for row in 27..=30 {
            let payload = [row, 0x19, 0x80];
            let absorbed = expected(&[&carried, &[0, 0xa0 + row], &3u32.to_le_bytes(), &payload]);
            let block = expected(&[&absorbed.1, &[1]]);
            let advance = expected(&[&absorbed.1, &[2]]);
            assert_eq!(opening.block(row, &payload), block.1);
            assert_eq!(take(), vec![absorbed, block, advance.clone()]);
            carried = advance.1;
            assert_eq!(opening.state, carried);
        }
        let payload = b"queries";
        let absorb = expected(&[
            &carried,
            &[0, 0xbf],
            &(payload.len() as u32).to_le_bytes(),
            payload,
        ]);
        let mut calls = vec![absorb.clone()];
        let mut blocks = [[0; 32]; 8];
        let mut advances = [[0; 32]; 8];
        carried = absorb.1;
        for i in 0..8 {
            let block = expected(&[&carried, &[1]]);
            let advance = expected(&[&carried, &[2]]);
            blocks[i] = block.1;
            advances[i] = advance.1;
            carried = advance.1;
            calls.extend([block, advance]);
        }
        let (queries, selected_state) =
            aspis_core::r0_transcript::queries_from_pairs(&blocks, &advances).unwrap();
        assert_eq!(opening.queries(31, payload).unwrap(), queries);
        assert_eq!(take(), calls);
        assert_eq!(opening.state, selected_state);
        let absorb = expected(&[&selected_state, &[0, 0xc0], &0u32.to_le_bytes(), &[]]);
        let block = expected(&[&absorb.1, &[1]]);
        let advance = expected(&[&absorb.1, &[2]]);
        opening.scalar_k(32, &[]);
        assert_eq!(take(), vec![absorb, block, advance.clone()]);
        assert_eq!(opening.state, advance.1);
    }
}
