// raw_vec/mod.rs:378-386
    pub(crate) fn try_reserve_exact(
        &mut self,
        len: usize,
        additional: usize,
    ) -> Result<(), TryReserveError> {
        // SAFETY: All calls on self.inner pass T::LAYOUT as the elem_layout
        unsafe { self.inner.try_reserve_exact(len, additional, T::LAYOUT) }
    }


// raw_vec/mod.rs:543-570
    unsafe fn finish_grow(
        &self,
        cap: usize,
        elem_layout: Layout,
    ) -> Result<NonNull<[u8]>, TryReserveError> {
        let new_layout = layout_array(cap, elem_layout)?;

        let memory = if let Some((ptr, old_layout)) = unsafe { self.current_memory(elem_layout) } {
            // FIXME(const-hack): switch to `debug_assert_eq`
            debug_assert!(old_layout.align() == new_layout.align());
            unsafe {
                // The allocator checks for alignment equality
                hint::assert_unchecked(old_layout.align() == new_layout.align());
                self.alloc.grow(ptr, old_layout, new_layout)
            }
        } else {
            self.alloc.allocate(new_layout)
        };

        // FIXME(const-hack): switch back to `map_err`
        match memory {
            Ok(memory) => Ok(memory),
            Err(_) => Err(AllocError { layout: new_layout, non_exhaustive: () }.into()),
        }
    }
}

impl<A: Allocator> RawVecInner<A> {

// raw_vec/mod.rs:575-581
        Self { ptr, cap: ZERO_CAP, alloc }
    }

    #[inline]
    fn try_with_capacity_in(
        capacity: usize,
        alloc: A,

// raw_vec/mod.rs:633-647
    const unsafe fn current_memory(&self, elem_layout: Layout) -> Option<(NonNull<u8>, Layout)> {
        if elem_layout.size() == 0 || self.cap.as_inner() == 0 {
            None
        } else {
            // We could use Layout::array here which ensures the absence of isize and usize overflows
            // and could hypothetically handle differences between stride and size, but this memory
            // has already been allocated so we know it can't overflow and currently Rust does not
            // support such types. So we can do better by skipping some checks and avoid an unwrap.
            unsafe {
                let alloc_size = elem_layout.size().unchecked_mul(self.cap.as_inner());
                let layout = Layout::from_size_align_unchecked(alloc_size, elem_layout.align());
                Some((self.ptr.into(), layout))
            }
        }
    }

// raw_vec/mod.rs:719-736
    unsafe fn try_reserve_exact(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError> {
        if self.needs_to_grow(len, additional, elem_layout) {
            // SAFETY: Precondition passed to caller
            unsafe {
                self.grow_exact(len, additional, elem_layout)?;
            }
        }
        unsafe {
            // Inform the optimizer that the reservation has succeeded or wasn't needed
            hint::assert_unchecked(!self.needs_to_grow(len, additional, elem_layout));
        }
        Ok(())
    }

// raw_vec/mod.rs:766-805
    const fn needs_to_grow(&self, len: usize, additional: usize, elem_layout: Layout) -> bool {
        additional > self.capacity(elem_layout.size()).wrapping_sub(len)
    }

    #[inline]
    #[rustc_const_unstable(feature = "const_heap", issue = "79597")]
    const unsafe fn set_ptr_and_cap(&mut self, ptr: NonNull<[u8]>, cap: usize) {
        // Allocators currently return a `NonNull<[u8]>` whose length matches
        // the size requested. If that ever changes, the capacity here should
        // change to `ptr.len() / size_of::<T>()`.
        self.ptr = Unique::from(ptr.cast());
        self.cap = unsafe { Cap::new_unchecked(cap) };
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    /// - The sum of `len` and `additional` must be greater than the current capacity
    unsafe fn grow_exact(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError> {
        if elem_layout.size() == 0 {
            // Since we return a capacity of `usize::MAX` when the type size is
            // 0, getting to here necessarily means the `RawVec` is overfull.
            return Err(CapacityOverflow.into());
        }

        let cap = len.checked_add(additional).ok_or(CapacityOverflow)?;

        // SAFETY: preconditions passed to caller
        let ptr = unsafe { self.finish_grow(cap, elem_layout)? };

        // SAFETY: `finish_grow` would have failed if `cap > isize::MAX`
        unsafe { self.set_ptr_and_cap(ptr, cap) };
        Ok(())
    }

// raw_vec/mod.rs:896-902
const fn layout_array(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveError> {
    // This is only used with `elem_layout`s which are those of real rust types,
    // which lets us use the much-simpler `repeat_packed`.
    debug_assert!(elem_layout.size() == elem_layout.pad_to_align().size());

    elem_layout.repeat_packed(cap).map_err(const |_| CapacityOverflow.into())
}

