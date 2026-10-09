//! Fallible verifier storage. Never materialize a large array before boxing it.
use super::Error;
use alloc::{boxed::Box, vec::Vec};
use core::mem::MaybeUninit;
pub fn filled<T: Copy>(n: usize, value: T) -> Result<Vec<T>, Error> {
    let mut out = Vec::new();
    out.try_reserve_exact(n).map_err(|_| Error::Allocation)?;
    out.resize(n, value);
    Ok(out)
}
pub fn uninit<T>() -> Result<Box<MaybeUninit<T>>, Error> {
    let mut out = Vec::<MaybeUninit<T>>::new();
    out.try_reserve_exact(1).map_err(|_| Error::Allocation)?;
    // MaybeUninit<T> has no initialization requirement and no destructor.
    unsafe {
        out.set_len(1);
    }
    let ptr = Box::into_raw(out.into_boxed_slice()) as *mut MaybeUninit<T>;
    // Exactly one element, with the same layout and allocation alignment.
    Ok(unsafe { Box::from_raw(ptr) })
}
