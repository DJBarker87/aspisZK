// ../core/src/alloc/layout.rs:73-119

    const fn is_size_alignment_valid(size: usize, alignment: Alignment) -> bool {
        size <= Self::max_size_for_alignment(alignment)
    }

    #[inline(always)]
    const fn max_size_for_alignment(alignment: Alignment) -> usize {
        // (power-of-two implies align != 0.)

        // Rounded up size is:
        //   size_rounded_up = (size + align - 1) & !(align - 1);
        //
        // We know from above that align != 0. If adding (align - 1)
        // does not overflow, then rounding up will be fine.
        //
        // Conversely, &-masking with !(align - 1) will subtract off
        // only low-order-bits. Thus if overflow occurs with the sum,
        // the &-mask cannot subtract enough to undo that overflow.
        //
        // Above implies that checking for summation overflow is both
        // necessary and sufficient.

        // SAFETY: the maximum possible alignment is `isize::MAX + 1`,
        // so the subtraction cannot overflow.
        unsafe { unchecked_sub(isize::MAX as usize + 1, alignment.as_usize()) }
    }

    /// Constructs a `Layout` from a given `size` and `alignment`,
    /// or returns `LayoutError` if any of the following conditions
    /// are not met:
    ///
    /// * `size`, when rounded up to the nearest multiple of `alignment`,
    ///   must not overflow `isize` (i.e., the rounded value must be
    ///   less than or equal to `isize::MAX`).
    #[unstable(feature = "ptr_alignment_type", issue = "102070")]
    #[inline]
    pub const fn from_size_alignment(
        size: usize,
        alignment: Alignment,
    ) -> Result<Self, LayoutError> {
        if Layout::is_size_alignment_valid(size, alignment) {
            // SAFETY: Layout::size invariants checked above.
            Ok(Layout { size, align: alignment })
        } else {
            Err(LayoutError)
        }
    }

// ../core/src/alloc/layout.rs:175-190
    pub const fn size(&self) -> usize {
        self.size
    }

    /// The minimum byte alignment for a memory block of this layout.
    ///
    /// The returned alignment is guaranteed to be a power of two.
    #[stable(feature = "alloc_layout", since = "1.28.0")]
    #[rustc_const_stable(feature = "const_alloc_layout_size_align", since = "1.50.0")]
    #[must_use = "this returns the minimum alignment, \
                  without modifying the layout"]
    #[inline]
    pub const fn align(&self) -> usize {
        self.align.as_usize()
    }


// ../core/src/alloc/layout.rs:206-211
    pub const fn new<T>() -> Self {
        <T as SizedTypeProperties>::LAYOUT
    }

    /// Produces layout describing a record that could be used to
    /// allocate backing structure for `T` (which could be a trait

// ../core/src/alloc/layout.rs:526-534
    pub const fn repeat_packed(&self, n: usize) -> Result<Self, LayoutError> {
        if let Some(size) = self.size.checked_mul(n) {
            // The safe constructor is called here to enforce the isize size limit.
            Layout::from_size_alignment(size, self.align)
        } else {
            Err(LayoutError)
        }
    }


