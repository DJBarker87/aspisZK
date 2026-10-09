//! Literal R0 code/chord formulas: SPEC.md §§3–5, snapshot 783aa3f97.
//!
//! Natural coefficients go directly into the encoders (no R16 transport).
//! This is a `no_std` arithmetic API, not a verifier or a Rust/Lean proof.
//! Matrices use fallible heap allocation; messages have fixed lengths. All
//! externally supplied indices/lengths and operational inverses are checked.

pub mod basis;
pub mod chord;
pub mod domain;
pub mod encoder;
pub mod fold;
pub mod scalar;

pub use scalar::CodeField;

pub const MESSAGE_LEN: usize = 1024;
pub const HALF_LEN: usize = 512;
pub const FINAL_LEN: usize = 256;
pub const WORD_LEN: usize = 1 << 20;
pub const FIBRE_COUNT: usize = 1 << 18;
pub type Message<E> = [E; MESSAGE_LEN];
pub type FinalMessage<E> = [E; FINAL_LEN];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    IndexOutOfRange,
    WrongLength,
    ZeroDenominator,
    Allocation,
}

#[cfg(test)]
mod tests;
