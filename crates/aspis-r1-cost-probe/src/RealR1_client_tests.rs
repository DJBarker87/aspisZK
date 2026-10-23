use super::*;
use alloc::vec::Vec;
use aspis_core::digest::LegacyHashFn;
use aspis_prover::{r0_fixture, HOST_HASH};

fn fixture(withdrawal: bool, direct: bool) {
    let fixture = r0_fixture::prepare(withdrawal);
    let mut id = [0u8; 16];
    getrandom::fill(&mut id).unwrap();
    let directory = std::env::temp_dir().join(alloc::format!("RealR1-client-{id:02x?}"));
    let mut ledger = DurableStateOnlyMaskNonceStore::open(&directory).unwrap();
    // Public addresses only: no account keys or funded accounts are created.
    let mut addresses = Vec::new();
    let started = std::time::Instant::now();
    let next_key = |k| {
        assert_eq!(k, addresses.len());
        let mut address = [0u8; 32];
        getrandom::fill(&mut address).unwrap();
        addresses.push(address);
        address
    };
    let result = if direct {
        let mut next_key = next_key;
        prover::prove_masked_retrying_with(fixture.public(), &fixture.compiled, Variant::S2, HOST_HASH, &mut ledger, |k| {
            StateOnlyAttemptSecrets::generate_for_mask_nonce(next_key(k)).map_err(|_| Error::Entropy)
        })
    } else {
        prove_for_proof_accounts(fixture.public(), &fixture.compiled, HOST_HASH, &mut ledger, next_key)
    }.expect("selected caller accepts within cap");
    std::println!("RealR1_CLIENT withdrawal={withdrawal} direct={direct} seconds={} attempts={}", started.elapsed().as_secs_f64(), result.attempts);
    assert_eq!(addresses.len(), result.attempts);
    assert!((1..=prover::ATTEMPT_CAP).contains(&result.attempts));
    let mut reserved = Vec::new();
    for entry in std::fs::read_dir(&directory).unwrap() {
        let record = std::fs::read(entry.unwrap().path()).unwrap();
        assert_eq!(&record[..16], b"ASPIS-MASK-V1\0\0\0");
        assert_eq!(record.len(), 80);
        reserved.push(<[u8; 32]>::try_from(&record[48..80]).unwrap());
    }
    assert_eq!(reserved.len(), addresses.len());
    assert!(addresses.iter().all(|a| reserved.contains(a)));
    let bytes = aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&fixture.statement).unwrap();
    let checkpoint = crate::verifier::tx1(fixture.public(), &bytes, &result.proof,
        crate::verifier::SPLIT, LegacyHashFn(HOST_HASH), None).unwrap();
    crate::verifier::tx2(&bytes, &result.proof, &checkpoint, LegacyHashFn(HOST_HASH), None).unwrap();
    crate::verifier::tx2_authenticated(&bytes, &result.proof, &checkpoint, LegacyHashFn(HOST_HASH), None).unwrap();
    crate::dense::verify(fixture.public(), &result.proof, HOST_HASH).unwrap();
    let repeated = prove_for_proof_accounts(fixture.public(), &fixture.compiled, HOST_HASH, &mut ledger, |_| addresses[result.attempts - 1]);
    assert!(matches!(repeated, Err(Error::Semantic)));
    assert_eq!(std::fs::read_dir(&directory).unwrap().count(), addresses.len());
    // Keep the reservation ledger: deleting it would enable nonce reuse.
    std::println!("RealR1_CLIENT retained_ledger={}", directory.display());
}

#[test]
fn transfer() { fixture(false, false); }

#[test]
fn withdrawal() { fixture(true, false); }

/// Explicit contemporaneous performance control for the D168 wall-time gate.
#[test]
fn direct_baseline_transfer() { fixture(false, true); }

#[test]
fn direct_baseline_withdrawal() { fixture(true, true); }
