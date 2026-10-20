#[derive(Clone,Copy,Debug,PartialEq,Eq)]
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
pub const MESSAGE_LEN:usize=1024;
pub type Message<T>=[T;MESSAGE_LEN];
pub mod opening;
pub mod transport;
