//! Unit tests of the D38.3 retry loop (cfg(test), feature `r1p-check`).
//! The forced-verdict hook replaces only the P_R1 verdict; every attempt is a
//! full proving attempt with fresh OS secrets and a durable nonce ledger.
use super::*;
use alloc::{collections::BTreeSet,vec::Vec};
use aspis_core::digest::LegacyHashFn;
use aspis_prover::{r0_fixture::{self,Fixture},state_only_entropy::DurableStateOnlyMaskNonceStore,HOST_HASH};

fn statement_bytes(fixture:&Fixture)->Vec<u8> {
    aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&fixture.statement).unwrap().to_vec()
}

fn fresh_ledger(label:&str)->std::path::PathBuf {
    let mut nonce=[0u8;16];getrandom::fill(&mut nonce).unwrap();
    let hex:alloc::string::String=nonce.iter().map(|b|alloc::format!("{b:02x}")).collect();
    let dir=std::env::temp_dir().join(alloc::format!("r1p-retry-{label}-{hex}"));
    assert!(!dir.exists());
    dir
}

fn verify_all(fixture:&Fixture,proof:&[u8]) {
    let public_bytes=statement_bytes(fixture);
    let checkpoint=crate::verifier::tx1(fixture.public(),&public_bytes,proof,11,LegacyHashFn(HOST_HASH),None).expect("tx1");
    crate::verifier::tx2(&public_bytes,proof,&checkpoint,LegacyHashFn(HOST_HASH),None).expect("tx2");
    crate::dense::verify(fixture.public(),proof,HOST_HASH).expect("dense verifier");
}

fn distinct<T:Ord+Clone>(v:impl Iterator<Item=T>)->usize { v.collect::<BTreeSet<_>>().len() }

/// Seven forced rejections, then acceptance: the eighth attempt is published,
/// every attempt has fresh secrets and a fresh C1 root, all eight nonces are
/// burned in the durable ledger, and the published proof verifies.
#[test]
fn forced_rejections_then_accept_publish_the_eighth_attempt() {
    let fixture=r0_fixture::prepare(false);
    let ledger_dir=fresh_ledger("forced");
    let mut ledger=DurableStateOnlyMaskNonceStore::open(&ledger_dir).unwrap();
    test_hooks::force(&[false,false,false,false,false,false,false,true]);
    let out=prove_masked_retrying(fixture.public(),&fixture.compiled,Variant::S2,HOST_HASH,&mut ledger).expect("eighth attempt accepted");
    let attempts=test_hooks::attempts();
    test_hooks::clear();
    assert_eq!(out.attempts,8);
    assert_eq!(attempts.len(),8);
    assert!(attempts.iter().all(|a|a.c1_root.is_some()));
    assert_eq!(attempts.iter().map(|a|a.forced_verdict).collect::<Vec<_>>(),[false,false,false,false,false,false,false,true].map(Some));
    assert_eq!(distinct(attempts.iter().map(|a|a.mask_nonce)),8,"fresh public nonce per attempt");
    assert_eq!(distinct(attempts.iter().map(|a|a.g_digest)),8,"fresh field-mask entropy per attempt");
    assert_eq!(distinct(attempts.iter().map(|a|a.salt_digest)),8,"fresh leaf-salt seed per attempt");
    assert_eq!(distinct(attempts.iter().map(|a|a.c1_root.unwrap())),8,"fresh C1 root per attempt");
    // The published proof carries the eighth attempt's C1 root (first 32 bytes after the header).
    assert_eq!(&out.proof[16..48],&attempts[7].c1_root.unwrap());
    drop(ledger);
    assert_eq!(std::fs::read_dir(&ledger_dir).unwrap().count(),8,"every attempt burned its nonce durably");
    verify_all(&fixture,&out.proof);
    let _=std::fs::remove_dir_all(&ledger_dir);
}

/// Eight forced rejections: `AttemptsExhausted`, no proof bytes, eight burned nonces.
#[test]
fn eight_rejections_exhaust_and_publish_nothing() {
    let fixture=r0_fixture::prepare(false);
    let ledger_dir=fresh_ledger("exhaust");
    let mut ledger=DurableStateOnlyMaskNonceStore::open(&ledger_dir).unwrap();
    test_hooks::force(&[false;9]);
    let out=prove_masked_retrying(fixture.public(),&fixture.compiled,Variant::S2,HOST_HASH,&mut ledger);
    let attempts=test_hooks::attempts();
    test_hooks::clear();
    assert!(matches!(out,Err(Error::AttemptsExhausted)));
    assert_eq!(attempts.len(),ATTEMPT_CAP,"the cap is 8: no ninth attempt");
    assert_eq!(distinct(attempts.iter().map(|a|a.c1_root.unwrap())),8);
    drop(ledger);
    assert_eq!(std::fs::read_dir(&ledger_dir).unwrap().count(),8);
    let _=std::fs::remove_dir_all(&ledger_dir);
}

/// The real extracted-checker path: no hook. The loop publishes a proof that
/// the strict two-transaction verifier and the dense verifier accept.
#[test]
fn real_check_publishes_a_verifying_proof() {
    let fixture=r0_fixture::prepare(false);
    let ledger_dir=fresh_ledger("real");
    let mut ledger=DurableStateOnlyMaskNonceStore::open(&ledger_dir).unwrap();
    test_hooks::clear();
    let _=take_check_times();
    let out=prove_masked_retrying(fixture.public(),&fixture.compiled,Variant::S2,HOST_HASH,&mut ledger).expect("P_R1 accepted within 8 attempts");
    let times=take_check_times();
    assert_eq!(times.len(),out.attempts,"one P_R1 check per attempt");
    verify_all(&fixture,&out.proof);
    drop(ledger);
    let _=std::fs::remove_dir_all(&ledger_dir);
}

/// P_R1 is defined for R1 (= S2) only; the loop refuses other variants.
#[test]
fn retry_loop_refuses_non_r1_variants() {
    let fixture=r0_fixture::prepare(false);
    let ledger_dir=fresh_ledger("variant");
    let mut ledger=DurableStateOnlyMaskNonceStore::open(&ledger_dir).unwrap();
    assert!(matches!(prove_masked_retrying(fixture.public(),&fixture.compiled,Variant::S1,HOST_HASH,&mut ledger),Err(Error::Semantic)));
    drop(ledger);
    let _=std::fs::remove_dir_all(&ledger_dir);
}
