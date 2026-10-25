#![no_std]
extern crate alloc;
#[path="NP6_sampler.rs"] mod sampler;
#[path="NP6_wire.rs"] mod r1_wire;
#[path="NP6_shipped.rs"] mod shipped;
#[path="NP6_reference.rs"] mod reference;
#[cfg(kani)] mod NP6_proofs;

#[cfg(kani)] mod NP6_construction;

#[cfg(kani)] mod NP6_success;

#[cfg(kani)] mod NP6_straight;

#[cfg(kani)] mod NP6_lengths;

#[cfg(kani)] mod NP6_steps;

#[cfg(kani)] mod NP6_characterization;

#[cfg(kani)] mod NP6_scalars;

#[cfg(kani)] mod NP6_errors;

#[cfg(kani)] mod NP6_frames;

#[cfg(kani)] mod NP6_ownership;

#[cfg(kani)] mod NP6_alloc;
