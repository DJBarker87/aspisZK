//! UNPROVED R1 COST PROBE. Focused strict/authenticated tx2 equivalence check.
use aspis_core::HashFn;
use aspis_prover::HOST_HASH;
use aspis_r1_cost_probe::{
    prover, trace,
    transport::Variant,
    verifier::{self, Error, HEADER},
};

fn main() {
    assert!(!cfg!(debug_assertions));
    let hash: HashFn = HOST_HASH;
    let fixture = aspis_prover::r0_fixture::prepare(false);
    let public = aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(
        &fixture.statement,
    )
    .unwrap();
    let seed = hash(&[b"UNPROVED:R1:authenticated-tx2-gate", &public]);
    let (proof, _) = prover::prove_masked_fixture(
        fixture.public(),
        &fixture.compiled,
        Variant::S2,
        hash,
        &seed,
    )
    .unwrap();

    trace::take();
    let checkpoint = verifier::tx1(fixture.public(), &public, &proof, 10, hash, None).unwrap();
    let _tx1_trace = trace::take();

    trace::take();
    let strict = verifier::tx2(&public, &proof, &checkpoint, hash, None);
    let mut strict_trace = trace::take();
    trace::take();
    let authenticated = verifier::tx2_authenticated(&public, &proof, &checkpoint, hash, None);
    let mut authenticated_trace = trace::take();
    assert_eq!(strict, Ok(()));
    assert_eq!(authenticated, Ok(()));
    strict_trace.sort();
    authenticated_trace.sort();
    assert_eq!(strict_trace, authenticated_trace);

    // Shape parsing accepts this opaque semantic-byte change; resume must
    // reject it because the checkpoint is bound to the original proof hash.
    let mut changed_proof = proof.clone();
    changed_proof[HEADER] ^= 1;
    trace::take();
    assert_eq!(
        verifier::tx2_authenticated(&public, &changed_proof, &checkpoint, hash, None),
        Err(Error::Checkpoint),
    );
    trace::take();

    let query_start = HEADER
        + verifier::SEMANTIC_BYTES
        + 29 * 32
        + 32
        + 7 * 32
        + 32
        + 7 * 32
        + Variant::S2.final_len() * 32;
    let mut noncanonical_query = proof.clone();
    noncanonical_query[query_start..query_start + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    trace::take();
    assert_eq!(
        verifier::tx2_authenticated(&public, &noncanonical_query, &checkpoint, hash, None),
        Err(Error::Checkpoint),
    );
    assert!(
        trace::take().is_empty(),
        "hash mismatch must reject before query arithmetic"
    );
    assert_eq!(
        verifier::tx2(&public, &noncanonical_query, &checkpoint, hash, None),
        Err(Error::Parse),
        "strict tx2 must retain its canonical query scan",
    );
    trace::take();

    let mut changed_public = public.clone();
    changed_public[0] ^= 1;
    assert_eq!(
        verifier::tx2_authenticated(&changed_public, &proof, &checkpoint, hash, None),
        Err(Error::Checkpoint),
    );

    for offset in [0, 8, 9, 10, 16, checkpoint.len() - 1] {
        let mut changed_checkpoint = checkpoint.clone();
        changed_checkpoint[offset] ^= 1;
        assert!(
            verifier::tx2_authenticated(&public, &proof, &changed_checkpoint, hash, None,).is_err()
        );
    }

    println!(
        "strict/authenticated tx2 acceptance and trace match; proof, public, and checkpoint mutations rejected; proof_bytes={} public_bytes={} checkpoint_bytes={} trace_entries={}",
        proof.len(),
        public.len(),
        checkpoint.len(),
        strict_trace.len(),
    );
}
