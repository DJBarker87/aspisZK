from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent; R=D.parents[2]
s=(D.parent/'rng-owner/prototype/lib.rs').read_text()
s=s[:s.index('\n\nimpl From<u8>')]
s=s.replace('u8>','getrandom::Error>').replace('Os(u8)','Os(getrandom::Error)')
# Change only error positions, never byte arrays.
s=s.replace('Result<(),u8>', 'Result<(),getrandom::Error>')
s=s.replace('StateOnlyAttemptEntropyError::Os(e)', 'StateOnlyAttemptEntropyError::from(e)')
s+='''
impl From<getrandom::Error> for StateOnlyAttemptEntropyError {
    fn from(value: getrandom::Error) -> Self { Self::Os(value) }
}
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Error { Parse,Semantic,Transcript,Relation,Merkle,Query,Checkpoint,Allocation,
    Rejected,AttemptsExhausted,Entropy }
pub struct RetriedProof { pub proof:Vec<u8>, pub audit:u64, pub attempts:usize }
pub const ATTEMPT_CAP:usize=8;
// The actual body and durable store remain a local interface, not a refinement premise.
pub fn selected_callback<N: FnMut(usize)->[u8;32]>(
    tape:Tape, mut proof_account:N, k:usize,
)->(Tape,N,Result<StateOnlyAttemptSecrets,Error>) {
    let nonce=proof_account(k);
    let (tape,status)=StateOnlyAttemptSecrets::generate_with(nonce,tape);
    (tape,proof_account,status.map_err(|_|Error::Entropy))
}
pub fn retry_attempt<N,L,B>(tape:Tape, proof_account:N, mut nonce_store:L, mut body:B,k:usize)
 ->(Tape,N,L,B,Result<RetriedProof,Error>)
 where N:FnMut(usize)->[u8;32],
 B:FnMut(StateOnlyAttemptSecrets,L)->(L,Result<(Vec<u8>,u64),Error>) {
    if k>=ATTEMPT_CAP { return (tape,proof_account,nonce_store,body,Err(Error::AttemptsExhausted)); }
    let (tape,proof_account,status)=selected_callback(tape,proof_account,k);
    let attempt=match status {Ok(a)=>a,Err(e)=>return (tape,proof_account,nonce_store,body,Err(e))};
    let (after_store,result)=body(attempt,nonce_store);
    nonce_store=after_store;
    match result {
        Ok((proof,audit))=>(tape,proof_account,nonce_store,body,Ok(RetriedProof{proof,audit,attempts:k+1})),
        Err(Error::Rejected)=>retry_attempt(tape,proof_account,nonce_store,body,k+1),
        Err(e)=>(tape,proof_account,nonce_store,body,Err(e)),
    }
}
pub fn prove_masked_retrying_with<N,L,B>(is_s2:bool,tape:Tape,proof_account:N,nonce_store:L,body:B)
 ->(Tape,N,L,B,Result<RetriedProof,Error>)
 where N:FnMut(usize)->[u8;32],
 B:FnMut(StateOnlyAttemptSecrets,L)->(L,Result<(Vec<u8>,u64),Error>) {
    if !is_s2 { return (tape,proof_account,nonce_store,body,Err(Error::Semantic)); }
    retry_attempt(tape,proof_account,nonce_store,body,0)
}
'''
(D/'prototype/lib.rs').write_text(s)
(D/'prototype/Cargo.toml').write_text('''[package]
name="prover-rw-rng-caller"
version="0.1.0"
edition="2021"
[workspace]
[lib]
path="lib.rs"
[dependencies]
zeroize="1"
getrandom="=0.3.4"
[[test]]
name="stateful"
path="runtime.rs"
[profile.release]
overflow-checks=true
''')
print(hashlib.sha256(s.encode()).hexdigest())
