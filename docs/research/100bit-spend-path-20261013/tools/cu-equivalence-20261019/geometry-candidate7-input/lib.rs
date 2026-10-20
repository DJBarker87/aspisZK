extern crate self as aspis_core;
extern crate alloc;
pub mod field;pub mod fast_domain;pub mod verifier;
pub mod r0 {pub const FIBRE_COUNT:usize=1<<18;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    IndexOutOfRange,
    WrongLength,
    ZeroDenominator,
    Allocation,
    NonCanonical,
    WrongField,
    InvalidPoints,
    QuotientNotInImage,
    RankDeficient,
    Parse,
    Semantic,
    Schedule,
    Sampler,
    Commitment,
    Authentication,
    V1,
    V2,
}

pub mod domain {include!("domain.rs");}}
use r0::domain;
pub mod old;pub mod new;
