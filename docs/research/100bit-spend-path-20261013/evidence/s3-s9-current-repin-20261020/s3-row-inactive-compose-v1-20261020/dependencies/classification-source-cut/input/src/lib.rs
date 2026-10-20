#![no_std]

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

pub mod opening {
use super::Error;

pub const COPY_ACTIVE_ROW_MASKS: [u16; 64] = [
    6144, 6144, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
    6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6144, 4097, 2048, 6145, 2049, 2048, 6145,
    2049, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145, 6145,
    6145, 6145, 6145, 6145, 6145, 4097, 6145, 6145, 4097, 26214, 26214, 26214, 26214, 26214, 26214,
    1749,
];

pub fn inactive(r: usize) -> Result<bool, Error> {
    if r >= 1024 {
        return Err(Error::IndexOutOfRange);
    }
    Ok((COPY_ACTIVE_ROW_MASKS[r / 16] >> (r % 16)) & 1 == 0)
}
}
}
