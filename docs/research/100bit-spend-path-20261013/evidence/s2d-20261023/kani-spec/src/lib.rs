// Generated verbatim by ../audit.py; release cfg only.
mod verifier {
pub enum Phase { Parsed,Semantic,SemanticPart(u8),Prepare,CheckpointRead,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite,Relation,Final }
pub type Observer=Option<fn(Phase)>;
}
use verifier::Phase;
fn observer()->verifier::Observer {
    #[cfg(feature="cu-profiling")] {Some(mark)}
    #[cfg(not(feature="cu-profiling"))] {None}
}
#[cfg(kani)]
mod S2D_checks {
    #[kani::proof]
    fn actual_release_observer_is_typed_none() {
        let result: Option<fn(super::Phase)> = super::observer();
        match result { None => (), Some(_) => panic!("release observer present") }
    }
}
