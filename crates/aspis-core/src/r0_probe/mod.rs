//! P1 unproved arithmetic cost experiment. Explicitly enabled beside R0.
pub use crate::r0::{
    basis, chord, domain, fold, heap, opening, transcript, transport, verifier, wire, Error,
};
#[cfg(all(feature = "r0-probe-reference", not(target_os = "solana")))]
pub mod equality_trace;
pub mod onchain;
#[cfg(all(feature = "r0-probe-reference", not(target_os = "solana")))]
pub mod onchain_re3;
pub mod structured;
