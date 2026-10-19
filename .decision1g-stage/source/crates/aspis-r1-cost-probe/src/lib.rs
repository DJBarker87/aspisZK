//! UNPROVED R1 COST PROBE. P2 only; no production entrypoint.
#![no_std]
extern crate alloc;
pub mod sampler;
pub mod semantic_wire;
pub mod semantic;
pub mod fast_domain;
pub mod fast_dots;
pub mod fast_pairing;

#[cfg(feature = "prover")]
extern crate std;
pub mod r1_wire;
pub mod r1_semantic;
pub mod trace;
pub mod transport;
pub mod weights;
pub mod transcript;
pub mod verifier;
#[cfg(feature = "prover")]
pub mod prover;
#[cfg(feature = "prover")]
pub mod dense;

#[cfg(feature="prover")] mod host_sumcheck;
#[cfg(feature="prover")] mod host_semantic;
#[cfg(feature="prover")] mod host_commitment;
