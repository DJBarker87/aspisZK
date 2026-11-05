//! Project the actual std slice-iterator step used by the shipped destructor.
//! This covers every suffix of an admitted 1024-word column without unrolling
//! the destructor or its sixteen independently allocated Vec buffers.
use aspis_core::field::M31;

#[kani::proof]
fn trace_drop_iterator_step() {
    let mut words = [M31(0); 1024];
    let start: usize = kani::any();
    let len: usize = kani::any();
    kani::assume(start <= 1024);
    kani::assume(len <= 1024 - start);
    let column = &mut words[start..start + len];
    let base = column.as_mut_ptr();
    let mut iter = column.iter_mut();
    match iter.next() {
        None => {
            assert_eq!(len, 0);
            assert_eq!(iter.as_slice().len(), 0);
        }
        Some(value) => {
            assert!(len > 0);
            assert_eq!(value as *mut M31, base);
            // The exact volatile-write expression in StateOnlyTraceFoundation::drop.
            unsafe { core::ptr::write_volatile(value, M31::ZERO) };
            assert_eq!(*value, M31::ZERO);
            assert_eq!(iter.as_slice().len(), len - 1);
            assert_eq!(iter.as_slice().as_ptr(), unsafe { base.add(1) });
        }
    }
}

/// The outer loop uses IntoIterator for &mut [Vec<M31>; 16], rather than a
/// scalar slice iterator. Check its next column and residual cursor directly.
#[kani::proof]
#[kani::unwind(18)]
fn trace_drop_outer_iterator_step() {
    let mut columns: [Vec<M31>; 16] = core::array::from_fn(|_| Vec::new());
    let base = columns.as_mut_ptr();
    let skip: usize = kani::any();
    kani::assume(skip <= 16);
    let mut iter = (&mut columns).into_iter();
    match iter.nth(skip) {
        None => {
            assert_eq!(skip, 16);
            assert_eq!(iter.as_slice().len(), 0);
        }
        Some(column) => {
            assert!(skip < 16);
            assert_eq!(column as *mut Vec<M31>, unsafe { base.add(skip) });
            assert_eq!(iter.as_slice().len(), 15 - skip);
            assert_eq!(iter.as_slice().as_ptr(), unsafe { base.add(skip + 1) });
        }
    }
}
