#![feature(allocator_api)]
extern crate alloc;
extern crate self as aspis_prover;
#[path="../../../crates/aspis-prover/src/host_arithmetic.rs"] pub mod host_arithmetic;
mod host_terminal_field;
#[path="host_copy_terminal_kani16.rs"] mod host_copy_terminal;
#[path="host_terminal_kani16.rs"] mod host_terminal;
#[path="reference_copy_terminal_kani16.rs"] mod reference_copy_terminal;
#[path="reference_terminal_kani16.rs"] mod reference_terminal;
mod reference_field;
mod reference_poseidon;
mod std194227;
#[path="../kmx/KMX_stubs.rs"] mod KMX_stubs;
#[cfg(kani)] mod equivalence16;

#[path="../../../crates/aspis-statement/src/poseidon2.rs"] pub mod poseidon2;
mod spend {use aspis_core::field::M31;
pub(crate) const DOMAIN_OWNER_KEY: M31 = M31(0x4153_0001);
pub(crate) const DOMAIN_NULLIFIER: M31 = M31(0x4153_0002);
pub(crate) const DOMAIN_NOTE: M31 = M31(0x4153_0003);
pub(crate) const DOMAIN_MERKLE_NODE: M31 = M31(0x4153_0005);
}

#[path="statement_copy_kani16.rs"] mod statement_copy16;

#[cfg(kani)] mod shared_callee16;
#[path="deployed_poseidon_kani16.rs"] mod deployed_poseidon16;
#[path="reference_poseidon_kani16.rs"] mod reference_poseidon16;

mod inputs16;
#[cfg(all(kani,not(feature="optimized-terminal")))] mod remaining_equivalence16;
