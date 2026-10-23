pub(crate) fn clear_private_salt(salt:&mut[u8;32]) {
    // SAFETY: the caller supplies a uniquely borrowed salt cell.
    unsafe {core::ptr::write_volatile(salt,[0;32]);}
}

pub(crate) fn volatile_clear_cell<T:Copy>(value:&mut T,zero:T) {
    // SAFETY: the caller supplies a uniquely borrowed cell.
    unsafe {core::ptr::write_volatile(value,zero);}
}
