//! Owned structural retry owner. No map, iterator, timing or entropy primitive.
//! The policy result retains all effects performed before the outcome.
pub enum Step<P,S,E> { Done(P,S), Retry(S), Stop(E,S) }
pub enum Run<P,S,E> { Published(P,usize,S), Stopped(E,S), Exhausted(S) }
pub trait Attempt<S,P,E> { fn attempt(index:usize,state:S)->Step<P,S,E>; }
pub fn retry<S,P,E,A:Attempt<S,P,E>>(fuel:usize,index:usize,state:S)->Run<P,S,E> {
    if fuel==0 { return Run::Exhausted(state); }
    match A::attempt(index,state) {
        Step::Done(proof,after)=>Run::Published(proof,index+1,after),
        Step::Retry(after)=>retry::<S,P,E,A>(fuel-1,index+1,after),
        Step::Stop(error,after)=>Run::Stopped(error,after),
    }
}
