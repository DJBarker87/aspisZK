//! Finite validation of the exact source controller with explicit fixture leaves.
//! No honest prover execution or production effect-silence claim.
use aspis_r1_cost_probe::verifier::Error;
use std::sync::{Arc,atomic::{AtomicUsize,Ordering}};
type Public<'a> = &'a ();
struct PoolV1PairForestMergedC1CompilationV1;
#[derive(Clone,Copy)] enum Variant { S2 }
type HashFn = ();
#[derive(Debug,PartialEq)] struct RetriedProof { proof:usize,audit:usize,attempts:usize }
#[derive(Debug,PartialEq)] struct DurableStateOnlyMaskNonceStore { calls:Vec<usize> }
struct StateOnlyAttemptSecrets { k:usize,code:u8 }
const ATTEMPT_CAP:usize=8;
fn prove_masked_attempt(_:Public<'_>,_:&PoolV1PairForestMergedC1CompilationV1,_:Variant,_:HashFn,a:StateOnlyAttemptSecrets,s:&mut DurableStateOnlyMaskNonceStore)->Result<(usize,usize),Error>{
 s.calls.push(a.k);
 match a.code {0=>Ok((a.k,91)),1=>Err(Error::Rejected),2=>Err(Error::Semantic),_=>unreachable!()}
}
// The complete frozen controller is inserted here byte-for-byte by the runner.
fn retry_attempt(
    public:Public<'_>,
    compiled:&PoolV1PairForestMergedC1CompilationV1,
    variant:Variant,
    hash:HashFn,
    nonce_store:&mut DurableStateOnlyMaskNonceStore,
    mut next_attempt:impl FnMut(usize)->Result<StateOnlyAttemptSecrets,Error>,
    k:usize,
)->Result<RetriedProof,Error> {
    if k>=ATTEMPT_CAP { return Err(Error::AttemptsExhausted); }
    let attempt=next_attempt(k)?;
    match prove_masked_attempt(public,compiled,variant,hash,attempt,nonce_store) {
        Ok((proof,audit))=>Ok(RetriedProof{proof,audit,attempts:k+1}),
        Err(Error::Rejected)=>retry_attempt(public,compiled,variant,hash,nonce_store,next_attempt,k+1),
        Err(e)=>Err(e),
    }
}
struct CallbackDrop(Arc<AtomicUsize>);
impl Drop for CallbackDrop {fn drop(&mut self){self.0.fetch_add(1,Ordering::SeqCst);}}
fn main(){
 let mut counts=[0usize;4];let mut cases=0usize;
 for start in 0..=8 {
  let remaining=8-start;
  for bits in 0..(1usize<<(remaining*2)) {
   let program:Vec<u8>=(0..remaining).map(|i|((bits>>(i*2))&3) as u8).collect();
   let callback_drops=Arc::new(AtomicUsize::new(0));let owned=CallbackDrop(callback_drops.clone());
   let mut called=Vec::new();let mut store=DurableStateOnlyMaskNonceStore{calls:Vec::new()};
   let called_ref=&mut called;let program_ref=&program;
   let callback=move |k:usize|{let _keep=&owned;called_ref.push(k);let code=program_ref[k-start];if code==3{Err(Error::Entropy)}else{Ok(StateOnlyAttemptSecrets{k,code})}};
   let actual=retry_attempt(&(),&PoolV1PairForestMergedC1CompilationV1,Variant::S2,(),&mut store,callback,start);
   // Independent finite oracle: first non-rejection wins, or the cap exhausts.
   let selected=program.iter().enumerate().find(|(_,code)|**code!=1);
   let mut expected_calls=Vec::new();let mut expected_bodies=Vec::new();
   let expected=match selected {
    Some((offset,&code))=>{for k in start..=start+offset{expected_calls.push(k);if k<start+offset||code!=3{expected_bodies.push(k);}}
     match code {0=>{counts[0]+=1;Ok(RetriedProof{proof:start+offset,audit:91,attempts:start+offset+1})},2=>{counts[1]+=1;Err(Error::Semantic)},3=>{counts[2]+=1;Err(Error::Entropy)},_=>unreachable!()}}
    None=>{counts[3]+=1;expected_calls.extend(start..8);expected_bodies.extend(start..8);Err(Error::AttemptsExhausted)}
   };
   assert_eq!(actual,expected);assert_eq!(called,expected_calls);assert_eq!(store.calls,expected_bodies);
   assert_eq!(callback_drops.load(Ordering::SeqCst),1);
   assert!(!matches!(actual,Err(Error::Rejected)));cases+=1;
  }
 }
 println!("{{\"cases\":{cases},\"success\":{},\"semantic\":{},\"entropy\":{},\"exhaustion\":{}}}",counts[0],counts[1],counts[2],counts[3]);
}
