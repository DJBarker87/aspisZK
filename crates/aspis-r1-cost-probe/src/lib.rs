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
/// Host client for the selected public proof-account nonce route (D162).
#[cfg(feature = "r1p-check")]
#[allow(non_snake_case)]
pub mod RealR1_client;
#[cfg(feature = "prover")]
pub mod dense;
/// G-sim (LOG D44.3): the explicit R1 simulator simE in the ideal game.
#[cfg(all(feature = "r1p-check", feature = "insecure-spend-fixture"))]
pub mod sim;

#[cfg(feature="prover")] mod host_sumcheck;
#[cfg(feature="prover")] mod host_semantic;
#[cfg(feature="prover")] mod host_commitment;
#[cfg(feature="prover")] mod host_tree;
#[cfg(feature="prover")] mod host_transcript;
#[cfg(feature="prover")] mod host_wire;
#[cfg(feature="prover")] mod host_compact;

// Adopted R1 proof format (PREREG-PROOF-SIZE-2, 2026-10-19): compact QM31
// storage and binary multiproofs. UNPROVED: see PROOF-SIZE-OBLIGATIONS.
pub mod multiproof;
pub mod compact;

#[cfg(not(feature="private-leaf-salts"))]
compile_error!("the adopted R1 proof format is defined over private leaf salts; enable `private-leaf-salts` (a default feature)");
#[cfg(all(feature="audit-eight-way",feature="prover"))]
compile_error!("`audit-eight-way` is audit-only: it is never combined with the prover (PREREG-PROOF-SIZE-2 item 4)");
#[cfg(all(feature="audit-eight-way",any(target_os="solana",feature="program-build")))]
compile_error!("`audit-eight-way` is audit-only: it is never built for a program (PREREG-PROOF-SIZE-2 item 4)");

#[cfg(all(feature = "ct-host-prover", feature = "program-build"))]
compile_error!("ct-host-prover is host-prover only, incompatible with program-build");

#[cfg(feature = "ct-host-prover")]
mod ct_pole;

// Fixed public-shape scheduling for the host CT adoption candidate.
#[cfg(feature="ct-host-prover")]
pub mod host_work;

#[cfg(all(feature = "prover", feature = "r1p-check"))]
mod prover_shared;

#[cfg(feature="prover")]
mod prover_helper_sum;

#[cfg(feature="prover")]
mod prover_powers;
#[cfg(feature="prover")] mod host_sampler;
#[cfg(feature="prover")] mod host_weights;

#[cfg(feature = "prover")]
pub use aspis_prover::host_forest;

#[cfg(feature = "prover")]
pub mod host_multilinear;

#[cfg(feature="prover")]
mod host_copy_terminal;

#[cfg(feature="prover")]
mod host_terminal;

#[cfg(feature="prover")]
pub mod host_public;

#[cfg(feature = "prover")]
mod host_terminal_field;
