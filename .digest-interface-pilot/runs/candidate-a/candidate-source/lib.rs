// CANDIDATE SOURCE: interface feasibility only; not unchanged release Rust.
#![no_std]
#![allow(dead_code)]
pub mod digest {
pub trait Digest32: Copy {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32];
}
}

pub mod r1_wire {
use crate::digest::Digest32;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Allocation,
    RowOrder { expected: u8, actual: u8 },
    InvalidRow,
    Tag { row: u8 },
    Length { row: u8 },
    NonCanonical { row: u8, value: usize },
    Boundary { round: usize },
    Terminal,
    EqualCirclePoints,
    TrailingBytes,
    Public,
}

/// Fresh R0 state, separate from Transcript's legacy all-zero IV. The
/// C1-time binding is exactly SPEC §9: public bytes and the C1 root in one
/// hash, with no profile/basis/nonce/registry pre-absorbs. Row 0 is empty.
#[derive(Clone)]
pub struct SemanticTranscript<H: Digest32> {
    state: [u8; 32],
    hash: H,
    next_row: u8,
}

impl<H: Digest32> SemanticTranscript<H> {
    fn sample_block_validated(&mut self, row: u8, framed: &[u8]) -> Result<[u8; 32], Error> {
        if row != self.next_row {
            return Err(Error::RowOrder {
                expected: self.next_row,
                actual: row,
            });
        }
        // Exactly one absorb, one squeeze and one advance. Both reads
        // use s_abs; advancing from the challenge block would be wrong.
        let absorbed = self.hash.digest(&[&self.state, &[0, 0xa0 + row], framed]);
        let block = self.hash.digest(&[&absorbed, &[1]]);
        self.state = self.hash.digest(&[&absorbed, &[2]]);
        self.next_row += 1;
        Ok(block)
    }
}
}
