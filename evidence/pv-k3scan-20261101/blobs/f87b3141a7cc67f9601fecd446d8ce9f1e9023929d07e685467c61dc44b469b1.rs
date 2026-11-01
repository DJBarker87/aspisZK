//! Owned byte-identical deployed host terminal. No reference law is claimed yet.
extern crate alloc;
#[path="../v244/host_terminal_field.rs"] mod host_terminal_field;
#[path="../v244/host_copy_terminal.rs"] mod host_copy_terminal;
#[path="../v244/host_terminal.rs"] pub mod host_terminal;

pub mod reference_terminal;

/// Owned entry with identical argument and complete Result signature.
pub fn reference227(public: reference_terminal::r0::Public<'_>, claims: &[[aspis_core::field::QM31;29];3], alpha: &[aspis_core::field::QM31;10], c: &aspis_core::state_only_prefix::r0::Challenges) -> Result<aspis_core::field::QM31,aspis_core::state_only_prefix::r0::Error> {
    public.terminal_qm31(claims,alpha,c)
}

#[path="../v244/std194227.rs"] pub mod std194227;

#[path="../v244/reference_copy_terminal.rs"] mod reference_copy_terminal;

#[path="../v244/reference_field.rs"] mod reference_field;
#[path="../v244/reference_poseidon.rs"] mod reference_poseidon;

use aspis_core::field::M31;
use aspis_core::state_only_prefix::r0::Error;
use aspis_statement::poseidon2::Digest;
use alloc::vec::Vec;
pub fn fields(out: &mut Vec<u8>, values: &[M31]) -> Result<(), Error> {
                for value in values {
                    if value.0 >= aspis_core::field::P {
                        return Err(Error::Public);
                    }
                    out.extend_from_slice(&value.0.to_le_bytes());
                }
                Ok(())
            }
pub fn frontier(out: &mut Vec<u8>, values: &[Digest; 20]) -> Result<(), Error> {
                fields(out, &values[0])?;
                fields(out, &values[1])?;
                fields(out, &values[2])?;
                fields(out, &values[3])?;
                fields(out, &values[4])?;
                fields(out, &values[5])?;
                fields(out, &values[6])?;
                fields(out, &values[7])?;
                fields(out, &values[8])?;
                fields(out, &values[9])?;
                fields(out, &values[10])?;
                fields(out, &values[11])?;
                fields(out, &values[12])?;
                fields(out, &values[13])?;
                fields(out, &values[14])?;
                fields(out, &values[15])?;
                fields(out, &values[16])?;
                fields(out, &values[17])?;
                fields(out, &values[18])?;
                fields(out, &values[19])?;
                Ok(())
            }

pub use aspis_statement::poseidon2;
pub mod original_poseidon14;
