//! Proof-only entry points; production sources and dependencies are unchanged.
use zeroize::{Zeroize, Zeroizing};
pub fn destroy32(value: Zeroizing<[u8; 32]>) { drop(value); }
pub fn destroy64(value: Zeroizing<[u8; 64]>) { drop(value); }

#[cfg(kani)]
fn zeroize_array<const N: usize>(mut bytes: [u8; N]) {
    bytes.zeroize();
    for b in bytes { assert_eq!(b, 0); }
}

#[cfg(kani)]
fn drop_retained<const N: usize>(bytes: [u8; N]) {
    // Complete initialized object in storage which outlives the destructor.
    // MaybeUninit prevents automatic second destruction; it is NOT evidence
    // that arbitrary uninitialized memory may be read.
    let mut storage = core::mem::MaybeUninit::new(Zeroizing::new(bytes));
    let owner = storage.as_mut_ptr();
    // Derive the exact inner allocation address while the owner is alive.
    // No layout/offset/transparent-representation assumption is made.
    let data = unsafe { (&mut **owner).as_mut_ptr() };
    // The temporary reference above ends before this unique destructor call.
    unsafe { core::ptr::drop_in_place(owner); }
    // Only u8 payload bytes, not padding or a reference to a dead owner.
    // The pinned destructor writes initialized zero u8s and frees no storage.
    // storage remains allocated here; no second drop of the owner occurs.
    for i in 0..N { assert_eq!(unsafe { data.add(i).read() }, 0); }
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(66)]
fn zeroize32() { zeroize_array(kani::any::<[u8; 32]>()); }
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(66)]
fn zeroize64() { zeroize_array(kani::any::<[u8; 64]>()); }
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(66)]
fn drop32() { drop_retained(kani::any::<[u8; 32]>()); }
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(66)]
fn drop64() { drop_retained(kani::any::<[u8; 64]>()); }

// Stronger physical relation: moved owner, untouched frame, and no surviving
// child pointer from before Drop. Only the byte OFFSET crosses destruction.
#[cfg(kani)]
fn moved_drop_frame<const N: usize>(value: Zeroizing<[u8; N]>, left: [u8; 16], right: [u8; 16]) {
    struct Frame<const M: usize> {
        left: [u8; 16],
        storage: core::mem::MaybeUninit<Zeroizing<[u8; M]>>,
        right: [u8; 16],
    }
    let mut frame = Frame { left, storage: core::mem::MaybeUninit::new(value), right };
    let owner = frame.storage.as_mut_ptr();
    let offset = {
        let data = unsafe { (&mut **owner).as_mut_ptr() };
        // Both pointers are within the same live, completely initialized
        // allocation. u8 alignment is one. No assumed Rust struct layout.
        let offset = unsafe { data.offset_from(owner.cast::<u8>()) };
        assert!(offset >= 0);
        let offset = offset as usize;
        assert!(offset + N <= core::mem::size_of::<Zeroizing<[u8; N]>>());
        offset
    };
    unsafe { core::ptr::drop_in_place(owner); }
    // Reacquire a root raw pointer from live MaybeUninit backing storage.
    // No child reference/raw pointer is reused across the destructor borrow.
    let post = frame.storage.as_mut_ptr().cast::<u8>();
    for i in 0..N { assert_eq!(unsafe { post.add(offset + i).read() }, 0); }
    assert_eq!(frame.left, left);
    assert_eq!(frame.right, right);
    // MaybeUninit does not auto-drop its now dead inner owner.
}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(66)]
fn moved_drop32_frame() {
    moved_drop_frame(Zeroizing::new(kani::any::<[u8;32]>()), kani::any(), kani::any());
}
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(66)]
fn moved_drop64_frame() {
    moved_drop_frame(Zeroizing::new(kani::any::<[u8;64]>()), kani::any(), kani::any());
}
