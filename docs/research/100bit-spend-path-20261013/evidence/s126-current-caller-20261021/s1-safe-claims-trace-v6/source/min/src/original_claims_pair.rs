use crate::r1_wire::{self as wire,Prefix,Error};
use alloc::boxed::Box;
use aspis_core::field::QM31;
#[inline(never)]
fn claims(prefix: &Prefix<'_>) -> Result<Box<[[QM31; 29]; 3]>, Error> {
    let record = prefix.validated_record(25)?;
    let mut out =
        aspis_core::r0::heap::uninit::<[[QM31; 29]; 3]>().map_err(|_| Error::Allocation)?;
    unsafe {
        for p in 0..3 {
            out.as_mut_ptr()
                .cast::<[QM31; 29]>()
                .add(p)
                .write(record.decode_k::<29>(p * 29)?);
        }
        Ok(out.assume_init())
    }
}

#[cfg(kani)]
pub(crate) fn run(prefix:&Prefix<'_>)->Result<Box<[[QM31;29];3]>,Error>{claims(prefix)}
