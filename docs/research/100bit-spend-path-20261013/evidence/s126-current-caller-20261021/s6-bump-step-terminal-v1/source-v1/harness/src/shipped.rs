use core::{mem::size_of,ptr::null_mut};

pub struct BumpAllocator {
    #[deprecated(
        since = "2.2.2",
        note = "This field should not be accessed directly. It will become private in future versions"
    )]
    pub start: usize,
    #[deprecated(
        since = "2.2.2",
        note = "This field should not be accessed directly. It will become private in future versions"
    )]
    pub len: usize,
}

impl BumpAllocator {
    /// Creates the allocator tied to a provided slice.
    /// This will not initialize the provided memory, except for the first
    /// bytes where the pointer is stored.
    ///
    /// # Safety
    /// As long as BumpAllocator or any of its allocations are alive,
    /// writing into or deallocating the arena will cause UB.
    ///
    /// Integer arithmetic in this global allocator implementation is safe when
    /// operating on the prescribed `HEAP_START_ADDRESS` and `HEAP_LENGTH`. Any
    /// other use may overflow and is thus unsupported and at one's own risk.
    #[inline]
    #[allow(clippy::arithmetic_side_effects)]
    pub unsafe fn new(arena: &mut [u8]) -> Self {
        debug_assert!(
            arena.len() > size_of::<usize>(),
            "Arena should be larger than usize"
        );

        // create a pointer to the start of the arena
        // that will hold an address of the byte following free space
        let pos_ptr = arena.as_mut_ptr() as *mut usize;
        // initialize the data there
        *pos_ptr = pos_ptr as usize + arena.len();

        #[allow(deprecated)] //we get to use deprecated pub fields
        Self {
            start: pos_ptr as usize,
            len: arena.len(),
        }
    }
}

/// Integer arithmetic in this global allocator implementation is safe when
/// operating on the prescribed `HEAP_START_ADDRESS` and `HEAP_LENGTH`. Any
/// other use may overflow and is thus unsupported and at one's own risk.
#[allow(clippy::arithmetic_side_effects)]
unsafe impl std::alloc::GlobalAlloc for BumpAllocator {
    #[inline]
    #[allow(deprecated)] //we get to use deprecated pub fields
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pos_ptr = self.start as *mut usize;
        let mut pos = *pos_ptr;
        if pos == 0 {
            // First time, set starting position
            pos = self.start + self.len;
        }
        pos = pos.saturating_sub(layout.size());
        pos &= !(layout.align().wrapping_sub(1));
        if pos < self.start + size_of::<*mut u8>() {
            return null_mut();
        }
        *pos_ptr = pos;
        pos as *mut u8
    }
    #[inline]
    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {
        // I'm a bump allocator, I don't free
    }
}

