// alloc.rs:205-215
    fn alloc_impl_runtime(layout: Layout, zeroed: bool) -> Result<NonNull<[u8]>, AllocError> {
        match layout.size() {
            0 => Ok(layout.dangling_ptr().cast_slice(0)),
            // SAFETY: `layout` is non-zero in size,
            size => unsafe {
                let raw_ptr = if zeroed { alloc_zeroed(layout) } else { alloc(layout) };
                let ptr = NonNull::new(raw_ptr).ok_or(AllocError)?;
                Ok(ptr.cast_slice(size))
            },
        }
    }

// alloc.rs:331-337
    const fn alloc_impl(&self, layout: Layout, zeroed: bool) -> Result<NonNull<[u8]>, AllocError> {
        core::intrinsics::const_eval_select(
            (layout, zeroed),
            Global::alloc_impl_const,
            Global::alloc_impl_runtime,
        )
    }

