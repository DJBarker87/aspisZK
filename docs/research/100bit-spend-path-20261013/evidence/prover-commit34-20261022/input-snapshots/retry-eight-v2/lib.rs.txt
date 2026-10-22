#![allow(unexpected_cfgs,non_snake_case)]
pub mod owner;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
#[cfg_attr(kani,derive(kani::Arbitrary))]
pub enum Error { Rejected, Semantic, AttemptsExhausted, Entropy, Other(u8) }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
#[cfg_attr(kani,derive(kani::Arbitrary))]
pub enum Variant { S1,S2 }
pub type Public<'a> = &'a u8;
pub type HashFn = ();
pub type PoolV1PairForestMergedC1CompilationV1 = ();
pub type StateOnlyAttemptSecrets = usize;
const ATTEMPT_CAP:usize=8;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
#[cfg_attr(kani,derive(kani::Arbitrary))]
pub struct Plan { pub entropy_error:bool,pub entropy:Error,pub attempt_error:bool,pub attempt:Error,pub proof:u8,pub audit:u8,pub delta:u64 }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct DurableStateOnlyMaskNonceStore { pub plans:[Plan;8],pub value:u64,pub calls:usize,pub order:[usize;8] }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct RetriedProof { pub proof:u8,pub audit:u8,pub attempts:usize }
fn prove_masked_attempt(_:Public<'_>,_:&(),_:Variant,_:HashFn,index:usize,store:&mut DurableStateOnlyMaskNonceStore)->Result<(u8,u8),Error> {
    let plan=store.plans[index];
    store.order[store.calls]=index;store.calls+=1;
    store.value^=plan.delta;
    if plan.attempt_error { Err(plan.attempt) } else { Ok((plan.proof,plan.audit)) }
}
include!("native-retry.rs");
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct State { pub store:DurableStateOnlyMaskNonceStore,pub entropy_calls:usize,pub entropy_order:[usize;8] }
pub struct Policy;
impl owner::Attempt<State,(u8,u8),Error> for Policy {
    fn attempt(index:usize,mut state:State)->owner::Step<(u8,u8),State,Error> {
        let plan=state.store.plans[index];
        state.entropy_order[state.entropy_calls]=index;state.entropy_calls+=1;
        if plan.entropy_error {return owner::Step::Stop(plan.entropy,state);}
        match prove_masked_attempt(&0,&(),Variant::S2,(),index,&mut state.store) {
            Ok(proof)=>owner::Step::Done(proof,state),
            Err(Error::Rejected)=>owner::Step::Retry(state),
            Err(error)=>owner::Step::Stop(error,state),
        }
    }
}
#[cfg(kani)]
mod proofs {
    use super::*;
    fn setup()->State {State{store:DurableStateOnlyMaskNonceStore{plans:kani::any(),value:kani::any(),calls:0,order:[0;8]},entropy_calls:0,entropy_order:[0;8]}}
    fn same_state(a:State,b:State) {
        assert_eq!(a.store.value,b.store.value);assert_eq!(a.store.calls,b.store.calls);
        assert_eq!(a.entropy_calls,b.entropy_calls);
        for i in 0..8 {
            assert_eq!(a.store.order[i],b.store.order[i]);assert_eq!(a.entropy_order[i],b.entropy_order[i]);
            let x=a.store.plans[i];let y=b.store.plans[i];
            assert_eq!(x.entropy_error,y.entropy_error);assert_eq!(x.entropy,y.entropy);
            assert_eq!(x.attempt_error,y.attempt_error);assert_eq!(x.attempt,y.attempt);
            assert_eq!(x.proof,y.proof);assert_eq!(x.audit,y.audit);assert_eq!(x.delta,y.delta);
        }
    }
    #[kani::proof]
    #[kani::unwind(10)]
    fn retry_eight() {
        let mut state=setup();let original=state;
        let plans=state.store.plans;
        let result=prove_masked_retrying_with(&0,&(),Variant::S2,(),&mut state.store,|index| {
            state.entropy_order[state.entropy_calls]=index;state.entropy_calls+=1;
            if plans[index].entropy_error {Err(plans[index].entropy)} else {Ok(index)}
        });
        let owned=owner::retry::<State,(u8,u8),Error,Policy>(8,0,original);
        match owned {
            owner::Run::Published((proof,audit),attempts,after)=> {assert_eq!(result,Ok(RetriedProof{proof,audit,attempts}));same_state(state,after);}
            owner::Run::Stopped(error,after)=> {assert_eq!(result,Err(error));same_state(state,after);}
            owner::Run::Exhausted(after)=> {assert_eq!(result,Err(Error::AttemptsExhausted));same_state(state,after);}
        }
    }
    #[kani::proof]
    fn entropy_rejected_aborts() {
        let mut state=setup();
        let result=prove_masked_retrying_with(&0,&(),Variant::S2,(),&mut state.store,|_|Err(Error::Rejected));
        assert_eq!(result,Err(Error::Rejected));assert_eq!(state.store.calls,0);
    }
}
