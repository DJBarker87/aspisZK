use std::sync::atomic::{AtomicU32,Ordering};
static PROBES:AtomicU32=AtomicU32::new(0);
static DRAWS:AtomicU32=AtomicU32::new(0);
#[unsafe(no_mangle)]
pub unsafe extern "C" fn getrandom(buf:*mut libc::c_void,len:usize,flags:u32)->isize {
    assert_eq!(flags,0);
    if len==0 { PROBES.fetch_add(1,Ordering::Relaxed); return 0; }
    DRAWS.fetch_add(1,Ordering::Relaxed);
    assert_eq!(len,64);
    std::ptr::write_bytes(buf.cast::<u8>(),0xa5,len);
    *libc::__errno_location()=libc::EIO;
    -1
}
#[unsafe(no_mangle)]
pub extern "C" fn pv_dispatch_counts()->u64 {
    ((PROBES.load(Ordering::Relaxed)as u64)<<32)|(DRAWS.load(Ordering::Relaxed)as u64)
}
