#![cfg_attr(kani, feature(allocator_api))]
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
#[cfg(feature = "r1p-check")]
pub mod sim;

#[cfg(feature="prover")] mod host_sumcheck;
#[cfg(feature="prover")] mod host_semantic;
#[cfg(feature="prover")] mod host_commitment;

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

#[cfg(kani)] mod NDI_controls;
