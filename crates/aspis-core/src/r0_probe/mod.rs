//! P1 unproved arithmetic cost experiment. Explicitly enabled beside R0.
pub use crate::r0::{basis, chord, domain, fold, heap, opening, transport, wire, Error};
#[cfg(all(feature = "r0-probe-reference", not(target_os = "solana")))]
pub mod equality_trace;
pub mod onchain;
#[cfg(all(feature = "r0-probe-reference", not(target_os = "solana")))]
pub mod onchain_re3;
pub mod structured;

#[cfg(not(feature = "r0-probe-c1"))]
pub use crate::r0::{prover, transcript, verifier};
#[cfg(feature = "r0-probe-c1")]
pub mod prover;
#[cfg(feature = "r0-probe-c1")]
pub mod transcript;
#[cfg(feature = "r0-probe-c1")]
pub mod verifier;
pub use crate::r0::{encoder, merkle, CodeField, FinalMessage, Message, FIBRE_COUNT, WORD_LEN};
#[cfg(feature = "r0-probe-c1")]
pub mod structured_k;

#[cfg(feature = "r0-probe-c2")]
pub mod relation;
