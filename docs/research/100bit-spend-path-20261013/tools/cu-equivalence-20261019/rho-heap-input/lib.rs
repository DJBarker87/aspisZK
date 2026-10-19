extern crate alloc;
pub mod r0 {
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
pub mod heap {use super::Error;use alloc::vec::Vec;
pub fn source_filled<T: Copy>(n: usize, value: T) -> Result<Vec<T>, Error> {
    let mut out = Vec::new();
    out.try_reserve_exact(n).map_err(|_| Error::Allocation)?;
    out.resize(n, value);
    Ok(out)
}
}
}
