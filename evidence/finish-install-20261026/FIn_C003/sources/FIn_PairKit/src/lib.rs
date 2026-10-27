#![allow(non_snake_case,dead_code,unexpected_cfgs)]
extern crate alloc;
#[path="FIn_weights.rs"] pub mod weights;
#[path="FIn_fast_pairing.rs"] pub mod fast_pairing;
#[path="FIn_transport.rs"] pub mod transport;
#[path="FIn_verifier.rs"] pub mod verifier;
#[path="FIn_trace.rs"] pub mod trace;
pub fn FIn_pair(w:&weights::Weights,alpha:&[aspis_core::field::WideExact],f:&[u8],kappa:aspis_core::field::WideExact)->Result<aspis_core::field::WideExact,verifier::Error> {w.pair(alpha,f,kappa)}
