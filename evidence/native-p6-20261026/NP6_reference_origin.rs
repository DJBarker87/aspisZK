use crate::r1_wire::{Prefix,Error};
use alloc::boxed::Box;
use aspis_core::field::QM31;
#[inline(never)]
fn claims(prefix: &Prefix<'_>) -> Result<Box<[[QM31; 29]; 3]>, Error> {
    let record = prefix.validated_record(25)?;
    let rows = aspis_core::r0::heap::filled(3, [QM31::ZERO; 29])
        .map_err(|_| Error::Allocation)?;
    let mut out: Box<[[QM31; 29]; 3]> = rows
        .into_boxed_slice()
        .try_into()
        .map_err(|_| Error::Allocation)?;
    out[0] = record.decode_k::<29>(0)?;
    out[1] = record.decode_k::<29>(29)?;
    out[2] = record.decode_k::<29>(58)?;
    Ok(out)
}
