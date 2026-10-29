//! Owned byte-identical deployed host terminal. No reference law is claimed yet.
extern crate alloc;
mod host_terminal_field;
mod host_copy_terminal;
pub mod host_terminal;

pub mod reference_terminal;

/// Owned entry with identical argument and complete Result signature.
pub fn reference227(public: reference_terminal::r0::Public<'_>, claims: &[[aspis_core::field::QM31;29];3], alpha: &[aspis_core::field::QM31;10], c: &aspis_core::state_only_prefix::r0::Challenges) -> Result<aspis_core::field::QM31,aspis_core::state_only_prefix::r0::Error> {
    public.terminal_qm31(claims,alpha,c)
}

pub mod std194227;

mod reference_copy_terminal;

mod reference_field;
mod reference_poseidon;
