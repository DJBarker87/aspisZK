// Exact production declaration cuts. Only module scaffolding and root wrappers are kit-owned.
#![no_std]
#![allow(dead_code)]
extern crate self as aspis_core;
pub use digest::Digest32;
pub mod digest {
pub trait Digest32: Copy {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32];
}
}
pub mod r1_wire {
use aspis_core::Digest32;
#[cfg(not(feature = "private-leaf-salts"))]
pub const DOMAIN: &[u8] = b"aspis:r0:20261009:v1";
#[cfg(feature = "private-leaf-salts")]
pub const DOMAIN: &[u8] = b"UNPROVED:R1:PRIVATE-SALTED:SEMANTIC:P3";

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

#[derive(Clone)]
pub struct SemanticTranscript<H: Digest32> {
    state: [u8; 32],
    hash: H,
    next_row: u8,
}

impl<H: Digest32> SemanticTranscript<H> {
    pub fn new(hash: H, public_bytes: &[u8], c1_root: &[u8; 32]) -> Result<Self, Error> {
        let length = u32::try_from(public_bytes.len()).map_err(|_| Error::Public)?;
        Ok(Self {
            state: hash.digest(&[DOMAIN, &[0], &length.to_le_bytes(), public_bytes, c1_root]),
            hash,
            next_row: 0,
        })
    }
    pub fn state(&self) -> [u8; 32] {
        self.state
    }
    pub fn next_row(&self) -> u8 {
        self.next_row
    }
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
// Extraction entrypoints only: bodies are one call to the unchanged methods.
pub fn source_new<H: Digest32>(hash: H, public_bytes: &[u8], root: &[u8; 32]) -> Result<SemanticTranscript<H>, Error> {
    SemanticTranscript::new(hash, public_bytes, root)
}
pub fn source_step<H: Digest32>(transcript: &mut SemanticTranscript<H>, row: u8, framed: &[u8]) -> Result<[u8; 32], Error> {
    transcript.sample_block_validated(row, framed)
}
pub fn source_inspect<H: Digest32>(transcript: &SemanticTranscript<H>) -> ([u8; 32], u8) {
    (transcript.state(), transcript.next_row())
}
}
