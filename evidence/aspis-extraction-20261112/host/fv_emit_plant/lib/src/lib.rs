//! X7 planted controls for the fault scans (gates iii and iv). Each function writes through a shape named in the
//! privacy lead's blind-spot list, or is a control that fv_x1b_mutiter.py / fv_x1b_writecalls.py already catch.
use core::cell::{Cell, RefCell, UnsafeCell};
// -------- reversed / backward mutable iteration
pub fn i1_iter_mut_rev(a: &mut [u32]) { for x in a.iter_mut().rev() { *x = 1; } }                 // control
pub fn i2_into_iter_rev(a: &mut [u32]) { for x in (&mut *a).into_iter().rev() { *x = 2; } }
pub fn i3_next_back(a: &mut [u32]) { let mut it = a.iter_mut(); while let Some(x) = it.next_back() { *x = 3; } }
pub fn i4_rchunks_mut(a: &mut [u32]) { for c in a.rchunks_mut(2) { c[0] = 4; } }
pub fn i5_helper(a: &mut [u32]) -> core::slice::IterMut<'_, u32> { a.iter_mut() }
pub fn i5_helper_rev(a: &mut [u32]) { for x in i5_helper(a).rev() { *x = 5; } }
pub fn i6_rev_of<I: DoubleEndedIterator>(i: I) -> core::iter::Rev<I> { i.rev() }
pub fn i6_split(a: &mut [u32]) { for x in i6_rev_of(a.iter_mut()) { *x = 6; } }
pub fn i7_chunks_mut_rev(a: &mut [u32]) { for c in a.chunks_mut(2).rev() { c[0] = 7; } }        // control
// -------- mutable state other than the account handles
pub fn s1_refcell_borrow_mut(c: &RefCell<u32>) { *c.borrow_mut() = 1; }                          // control
pub fn s2_refcell_replace(c: &RefCell<u32>) -> u32 { c.replace(2) }
pub fn s3_refcell_replace_with(c: &RefCell<u32>) -> u32 { c.replace_with(|v| *v + 3) }
pub fn s4_refcell_swap(c: &RefCell<u32>, d: &RefCell<u32>) { c.swap(d) }
pub fn s5_refcell_take(c: &RefCell<u32>) -> u32 { c.take() }
pub fn s6_cell_set(c: &Cell<u32>) { c.set(6) }
pub fn s7_cell_replace(c: &Cell<u32>) -> u32 { c.replace(7) }
pub fn s8_cell_swap(c: &Cell<u32>, d: &Cell<u32>) { c.swap(d) }
pub fn s9_cell_take(c: &Cell<u32>) -> u32 { c.take() }
pub fn s10_unsafecell_get(c: &UnsafeCell<u32>) { unsafe { *c.get() = 10 } }
pub fn s11_ptr_write(p: *mut u32) { unsafe { core::ptr::write(p, 11) } }
pub fn s12_ptr_method_write(p: *mut u32) { unsafe { p.write(12) } }
pub fn s13_ptr_copy(src: *const u32, dst: *mut u32) { unsafe { core::ptr::copy_nonoverlapping(src, dst, 1) } }
