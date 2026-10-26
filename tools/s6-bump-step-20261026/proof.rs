#![allow(deprecated)]
mod shipped;

/// Owned, offset-only reference. No allocation, pointer read or global state.
pub fn step(initial: usize, length: usize, bytes: usize, align: usize) -> Option<usize> {
    let cursor = if initial == 0 { length } else { initial };
    let available = cursor.checked_sub(bytes)?;
    let next = (available / align) * align;
    if next < core::mem::size_of::<usize>() { None } else { Some(next) }
}

#[cfg(kani)]
mod proofs {
    use super::{shipped::BumpAllocator, step};
    use core::alloc::{GlobalAlloc, Layout};

    fn run(negative: bool) {
        assert!(core::mem::size_of::<usize>() == 8);
        // Only the allocator's cursor word is read. Remaining arena bytes
        // intentionally stay uninitialized, exactly as allowed by the API.
        const LENGTH: usize = 262144;
        let arena_layout = Layout::from_size_align(LENGTH, 8).unwrap();
        let arena = unsafe { std::alloc::alloc(arena_layout) };
        assert!(!arena.is_null()); // Kani's ordinary successful arena allocation.
        let pointer = arena.cast::<usize>();
        let start = pointer as usize;
        let initial: usize = kani::any();
        kani::assume(initial == 0 || (8 <= initial && initial <= LENGTH));
        let bytes: usize = kani::any();
        kani::assume(1 <= bytes && bytes <= LENGTH);
        let exponent: u8 = kani::any();
        kani::assume(exponent <= 3);
        let align = 1usize << exponent;
        let layout = Layout::from_size_align(bytes, align).unwrap();
        let before = if initial == 0 { 0 } else { start + initial };
        unsafe { pointer.write(before); }
        let allocator = BumpAllocator { start, len: LENGTH };
        let actual = unsafe { allocator.alloc(layout) };
        let after = unsafe { pointer.read() };
        match step(initial, LENGTH, bytes, align) {
            None => {
                assert!(actual.is_null());
                assert!(after == before);
                kani::cover!(true, "allocation rejected without cursor write");
            }
            Some(next) => {
                let expected = if negative { next + 8 } else { next };
                assert!(actual as usize == start + expected);
                assert!(after == start + next);
                assert!(8 <= next && next <= LENGTH);
                assert!(next + bytes <= if initial == 0 { LENGTH } else { initial });
                assert!((if initial == 0 { LENGTH } else { initial }) <= next + bytes + 7);
                assert!((actual as usize) % align == 0);
                kani::cover!(true, "allocation succeeded with aligned cursor");
                kani::cover!(initial == 0, "fresh cursor initialized");
                kani::cover!(initial != 0, "existing cursor advanced");
                // Invoke the actual deallocator; its no-op behavior matters
                // for cumulative rather than live-byte capacity accounting.
                unsafe { allocator.dealloc(actual, layout); }
                assert!(unsafe { pointer.read() } == after);
            }
        }
        unsafe { std::alloc::dealloc(arena, arena_layout); }
    }

    #[kani::proof]
    #[kani::unwind(4)]
    fn bump_step_matches_owned() { run(false); }

    #[kani::proof]
    #[kani::unwind(4)]
    fn bump_step_negative_control() { run(true); }
}
