//! Finite native binding probe, not an honest-prover run.
use anyhow::{Result,anyhow};
use aspis_r1_cost_probe::verifier::Error;
fn err(e:impl std::fmt::Debug)->anyhow::Error{anyhow!("{e:?}")}
fn main()->Result<()> {
 let n:usize=std::env::args().nth(1).unwrap().parse().unwrap();
 let e=match n {0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,
 3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,
 7=>Error::Allocation,8=>Error::Rejected,9=>Error::AttemptsExhausted,
 10=>Error::Entropy,_=>return Ok(())};
 Err(err(e))
}
