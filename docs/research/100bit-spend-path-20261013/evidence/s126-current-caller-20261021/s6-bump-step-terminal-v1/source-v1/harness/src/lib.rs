#![allow(deprecated)]
mod shipped;

/// Owned, offset-only reference. No allocation, pointer read or global state.
pub fn step(initial: usize, length: usize, bytes: usize, align: usize) -> Option<usize> {
    let cursor = if initial == 0 { length } else { initial };
    let available = cursor.checked_sub(bytes)?;
    let next = available & !(align - 1);
    if next < core::mem::size_of::<usize>() { None } else { Some(next) }
}

#[cfg(kani)]
mod proofs {
    use super::{shipped::BumpAllocator, step};
    use core::{alloc::{GlobalAlloc, Layout}, mem::MaybeUninit};

    fn run(negative: bool) {
        assert!(core::mem::size_of::<usize>() == 8);
        // Only the allocator's cursor word is read. Remaining arena bytes
        // intentionally stay uninitialized, exactly as allowed by the API.
        let mut arena = MaybeUninit::<[usize; 1024]>::uninit();
        let pointer = arena.as_mut_ptr().cast::<usize>();
        let start = pointer as usize;
        let initial: usize = kani::any();
        kani::assume(initial == 0 || (8 <= initial && initial <= 8192));
        let bytes: usize = kani::any();
        kani::assume(1 <= bytes && bytes <= 8192);
        let exponent: u8 = kani::any();
        kani::assume(exponent <= 3);
        let align = 1usize << exponent;
        let layout = Layout::from_size_align(bytes, align).unwrap();
        let before = if initial == 0 { 0 } else { start + initial };
        unsafe { pointer.write(before); }
        let allocator = BumpAllocator { start, len: 8192 };
        let actual = unsafe { allocator.alloc(layout) };
        let after = unsafe { pointer.read() };
        match step(initial, 8192, bytes, align) {
            None => {
                assert!(actual.is_null());
                assert!(after == before);
                kani::cover!(true, "allocation rejected without cursor write");
            }
            Some(next) => {
                let expected = if negative { next + 8 } else { next };
                assert!(actual as usize == start + expected);
                assert!(after == start + next);
                assert!(8 <= next && next <= 8192);
                assert!(next + bytes <= if initial == 0 { 8192 } else { initial });
                assert!((actual as usize) % align == 0);
                kani::cover!(true, "allocation succeeded with aligned cursor");
                // Invoke the actual deallocator; its no-op behavior matters
                // for cumulative rather than live-byte capacity accounting.
                unsafe { allocator.dealloc(actual, layout); }
                assert!(unsafe { pointer.read() } == after);
            }
        }
    }

    #[kani::proof]
    #[kani::unwind(4)]
    fn bump_step_matches_owned() { run(false); }

    #[kani::proof]
    #[kani::unwind(4)]
    fn bump_step_negative_control() { run(true); }
}
