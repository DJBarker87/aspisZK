// Raw-caller adversarial input probe. The malformed branch is deliberately
// NOT evidence of two admitted BuilderCanonical witnesses.
use aspis_prover::{r0_fixture, state_only_entropy::DurableStateOnlyMaskNonceStore, HOST_HASH};
use aspis_r1_cost_probe::{RealR1_client::prove_for_proof_accounts, verifier::Error};
fn programmed_oracle(parts: &[&[u8]]) -> [u8;32] {
    if parts.len()==2 && parts[0].len()==32 && parts[1]==[1] { [0;32] }
    else { HOST_HASH(parts) }
}
fn main() {
    let malformed = std::env::args().nth(1).as_deref() == Some("malformed");
    let directory = std::env::args().nth(2).expect("retained ledger directory");
    let mut f = r0_fixture::prepare(false);
    if malformed { f.compiled.semantic_c1.c1[0].pop(); }
    let mut ledger = DurableStateOnlyMaskNonceStore::open(&directory).unwrap();
    let mut calls = 0usize;
    let public_bytes = f.public().public_bytes().unwrap();
    println!("public_digest={:02x?}",HOST_HASH(&[&public_bytes]));
    let hash = if std::env::var_os("PV_PROGRAM_ORACLE").is_some() {programmed_oracle} else {HOST_HASH};
    let result = prove_for_proof_accounts(f.public(), &f.compiled, hash, &mut ledger, |i| {
        assert_eq!(i,calls);
        calls += 1;
        [1+i as u8;32]
    });
    let status = match result {
        Ok(p) => format!("ok:{}",p.attempts),
        Err(e) => match e {Error::Entropy=>"Entropy".into(), Error::Semantic=>"Semantic".into(),_=>"other".into()}
    };
    println!("malformed={malformed} callbacks={calls} result={status} ledger={directory}");
}
