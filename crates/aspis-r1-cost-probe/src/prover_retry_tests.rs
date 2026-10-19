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

// ---------------------------------------------------------------------------
// LOG D73.4 items 1 and 2: a LogUp pole (Lean `¬ VR1`) and mask exhaustion
// (Lean `exh`) are rejected attempts, as in `realGameP` (R1Z/GamesR1P.lean:184).

/// A pole on attempt 1: the attempt consumes one of the eight, runs no P_R1
/// check, publishes nothing, and attempt 2 (fresh secrets, fresh nonce) is
/// published and verifies.
#[test]
fn pole_on_first_attempt_is_a_rejected_attempt() {
    let fixture=r0_fixture::prepare(false);
    let ledger_dir=fresh_ledger("pole1");
    let mut ledger=DurableStateOnlyMaskNonceStore::open(&ledger_dir).unwrap();
    test_hooks::clear();
    test_hooks::force(&[true;8]);
    test_hooks::force_poles(&[1]);
    let out=prove_masked_retrying(fixture.public(),&fixture.compiled,Variant::S2,HOST_HASH,&mut ledger).expect("attempt 2 accepted");
    let attempts=test_hooks::attempts();
    test_hooks::clear();
    assert_eq!(out.attempts,2,"the pole consumed attempt 1");
    assert_eq!(attempts.len(),2);
    assert!(attempts[0].pole && attempts[0].c1_root.is_none() && attempts[0].forced_verdict.is_none(),"no P_R1 check on the pole attempt");
    assert!(!attempts[1].pole && attempts[1].forced_verdict==Some(true));
    assert_eq!(distinct(attempts.iter().map(|a|a.mask_nonce)),2,"fresh nonce after a pole");
    assert_eq!(distinct(attempts.iter().map(|a|a.g_digest)),2,"fresh field-mask entropy after a pole");
    assert_eq!(distinct(attempts.iter().map(|a|a.salt_digest)),2,"fresh leaf-salt seed after a pole");
    assert_eq!(&out.proof[16..48],&attempts[1].c1_root.unwrap(),"the published proof is attempt 2's");
    drop(ledger);
    assert_eq!(std::fs::read_dir(&ledger_dir).unwrap().count(),2,"the pole attempt burned its nonce");
    verify_all(&fixture,&out.proof);
    let _=std::fs::remove_dir_all(&ledger_dir);
}

/// Seven P_R1 rejections, then a pole on attempt 8: `AttemptsExhausted`, no
/// ninth attempt, no proof bytes, eight distinct burned nonces.
#[test]
fn pole_on_eighth_attempt_exhausts_and_publishes_nothing() {
    let fixture=r0_fixture::prepare(false);
    let ledger_dir=fresh_ledger("pole8");
    let mut ledger=DurableStateOnlyMaskNonceStore::open(&ledger_dir).unwrap();
    test_hooks::clear();
    test_hooks::force(&[false;7]);
    test_hooks::force_poles(&[8]);
    let out=prove_masked_retrying(fixture.public(),&fixture.compiled,Variant::S2,HOST_HASH,&mut ledger);
    let attempts=test_hooks::attempts();
    test_hooks::clear();
    assert!(matches!(out,Err(Error::AttemptsExhausted)),"nothing is published");
    assert_eq!(attempts.len(),ATTEMPT_CAP,"no ninth attempt");
    assert!(attempts[..7].iter().all(|a|!a.pole && a.forced_verdict==Some(false)));
    assert!(attempts[7].pole && attempts[7].forced_verdict.is_none());
    assert_eq!(distinct(attempts.iter().map(|a|a.mask_nonce)),8);
    assert_eq!(distinct(attempts.iter().map(|a|a.g_digest)),8);
    drop(ledger);
    assert_eq!(std::fs::read_dir(&ledger_dir).unwrap().count(),8);
    let _=std::fs::remove_dir_all(&ledger_dir);
}

/// Mask exhaustion on attempt 1 (forced right after the nonce reservation):
/// a rejected attempt; attempt 2 is published and verifies.
#[test]
fn mask_exhaustion_on_first_attempt_is_a_rejected_attempt() {
    let fixture=r0_fixture::prepare(false);
    let ledger_dir=fresh_ledger("exh1");
    let mut ledger=DurableStateOnlyMaskNonceStore::open(&ledger_dir).unwrap();
    test_hooks::clear();
    test_hooks::force(&[true;8]);
    test_hooks::force_exhaustion(&[1]);
    let out=prove_masked_retrying(fixture.public(),&fixture.compiled,Variant::S2,HOST_HASH,&mut ledger).expect("attempt 2 accepted");
    let attempts=test_hooks::attempts();
    test_hooks::clear();
    assert_eq!(out.attempts,2);
    assert_eq!(attempts.len(),2);
    assert!(attempts[0].exhausted && attempts[0].c1_root.is_none());
    assert_eq!(distinct(attempts.iter().map(|a|a.mask_nonce)),2);
    assert_eq!(&out.proof[16..48],&attempts[1].c1_root.unwrap());
    drop(ledger);
    assert_eq!(std::fs::read_dir(&ledger_dir).unwrap().count(),2);
    verify_all(&fixture,&out.proof);
    let _=std::fs::remove_dir_all(&ledger_dir);
}

/// The unforced pole test is Lean's `NoPole`: every slot of every active row,
/// weighted or not. Every value the prover's copy rows hold (weighted or not)
/// is a Lean slot value of the same row and side; a weighted one is also an
/// `ActivePole` of the helper builder; a zero-weight, overwritten or empty
/// slot value is a Lean pole that the weighted-only builder does not see.
fn check_no_pole_on(withdrawal:bool) {
    use aspis_core::field::{M31,CM31,QM31};
    use aspis_statement::{build_copy_logup_helper,LogUpError,pool_v1::{pair_forest_trace::pool_v1_pair_forest_copy_rows_v1,pool_v1_pair_forest_copy_active_row_masks_v1}};
    let fixture=r0_fixture::prepare(withdrawal);
    let append=fixture.public().transition().live_snapshot.next_pair_index;
    let lambda=QM31{c0:CM31::new(M31(1_234_567),M31(7_654_321)),c1:CM31::new(M31(99),M31(101))};
    let rows=pool_v1_pair_forest_copy_rows_v1(&fixture.compiled.trace,append,lambda).unwrap();
    let lean=crate::host_semantic::lean_copy_row_values(&fixture.compiled.trace,lambda).unwrap();
    let masks=pool_v1_pair_forest_copy_active_row_masks_v1().unwrap();
    let chi=QM31{c0:CM31::new(M31(31_415_926),M31(27_182_818)),c1:CM31::new(M31(16_180_339),M31(14_142_135))};
    assert!(crate::host_semantic::no_pole(&fixture.compiled,lambda,chi).unwrap(),"a generic chi is not a pole");
    assert!(!crate::host_semantic::no_pole(&fixture.compiled,lambda,QM31::ZERO).unwrap(),"0 is a Lean pole: some active slot is unused");
    let weighted_values:Vec<QM31>=rows.iter().flat_map(|r|r.producer_values.iter().zip(&r.producer_weights).chain(r.consumer_values.iter().zip(&r.consumer_weights))).filter(|(_,w)|**w!=M31::ZERO).map(|(v,_)|*v).collect();
    let (mut lean_slots,mut missed)=(0usize,0usize);
    let mut missed_nonzero:Vec<QM31>=Vec::new();
    for (row,r) in rows.iter().enumerate() {
        let active=masks[row>>4]&(1<<(row&15))!=0;
        if !active {
            assert!(r.producer_weights.iter().chain(&r.consumer_weights).all(|w|*w==M31::ZERO));
            assert!(lean[row].iter().flatten().all(|v|*v==QM31::ZERO));
            continue;
        }
        for (side,rust) in [r.producer_values,r.consumer_values].iter().enumerate() {
            for v in rust { assert!(*v==QM31::ZERO || lean[row][side].contains(v),"row {row} side {side}: a prover row value is a Lean slot value"); }
            for v in &lean[row][side] {
                lean_slots+=1;
                assert!(!crate::host_semantic::no_pole(&fixture.compiled,lambda,*v).unwrap(),"row {row}: every active Lean slot value is a pole");
                if weighted_values.contains(v) {
                    assert!(matches!(build_copy_logup_helper(&rows,*v),Err(LogUpError::ActivePole{..})));
                } else {
                    missed+=1;
                    if *v!=QM31::ZERO && !missed_nonzero.contains(v) { missed_nonzero.push(*v); }
                    assert!(build_copy_logup_helper(&rows,*v).is_ok(),"the weighted-only builder misses this Lean pole");
                }
            }
        }
    }
    std::eprintln!("withdrawal={withdrawal}: active Lean slots {lean_slots}, of which not weighted-builder poles {missed}; distinct nonzero such values {}",missed_nonzero.len());
    assert!(!missed_nonzero.is_empty(),"some zero-weight or overwritten endpoint value is a Lean pole the builder misses");
}

#[test]
fn no_pole_is_lean_no_pole_transfer() { check_no_pole_on(false); }

#[test]
fn no_pole_is_lean_no_pole_withdrawal() { check_no_pole_on(true); }

/// The static slot used by `lean_copy_row_values` (registry order per row and
/// side) is the slot of the generated terminal constants
/// (pair_forest_copy_terminal_constants.rs `COPY_LINKS`, transcribed by the
/// Lean R0P/CopyConstants.lean), link by link and in the same order and tag.
#[test]
fn static_slots_are_the_terminal_constants() {
    use aspis_statement::pool_v1::pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1;
    let text=include_str!("../../aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs");
    let num=|s:&str,key:&str|->u32 { let i=s.find(key).unwrap()+key.len(); s[i..].trim_start().split(|c:char|!c.is_ascii_digit()).next().unwrap().parse().unwrap() };
    let constants:Vec<(u32,u32,u32,u32,u32)>=text.lines().filter(|l|l.trim_start().starts_with("CompiledPoolV1PairForestLink {")).map(|l|{
        let (p,c)=l.split_at(l.find("consumer:").unwrap());
        (num(l,"tag:"),num(p,"row:"),num(p,"slot:"),num(c,"row:"),num(c,"slot:"))
    }).collect();
    let registry=build_pool_v1_pair_forest_copy_registry_v1().unwrap();
    assert_eq!(constants.len(),registry.len());
    let mut arity=alloc::vec![[0u32;2];1024];
    for (link,(tag,prow,pslot,crow,cslot)) in registry.iter().zip(&constants) {
        assert_eq!(link.tag.0,*tag);
        assert_eq!((u32::from(link.producer.row),u32::from(link.consumer.row)),(*prow,*crow));
        let ps=arity[link.producer.row as usize][0];arity[link.producer.row as usize][0]+=1;
        let cs=arity[link.consumer.row as usize][1];arity[link.consumer.row as usize][1]+=1;
        assert_eq!((ps,cs),(*pslot,*cslot),"link tag {tag}");
    }
    std::eprintln!("{} links: registry-order slots equal the terminal constants",registry.len());
}
