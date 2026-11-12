//! X7 planted controls, dependency form: every planted function is called from this crate, so Charon reads
//! x7_plant_lib as a dependency (optimized MIR), as it reads the Aspis library crates in the program emissions.
use core::cell::{Cell, RefCell, UnsafeCell};
use x7_plant_lib::*;
pub fn root_all(a: &mut [u32], r: &RefCell<u32>, r2: &RefCell<u32>, c: &Cell<u32>, c2: &Cell<u32>, u: &UnsafeCell<u32>, p: *mut u32, q: *const u32) -> u32 {
    i1_iter_mut_rev(a); i2_into_iter_rev(a); i3_next_back(a); i4_rchunks_mut(a); i5_helper_rev(a); i6_split(a); i7_chunks_mut_rev(a);
    s1_refcell_borrow_mut(r); s4_refcell_swap(r, r2); s6_cell_set(c); s8_cell_swap(c, c2); s10_unsafecell_get(u);
    s11_ptr_write(p); s12_ptr_method_write(p); s13_ptr_copy(q, p);
    s2_refcell_replace(r) + s3_refcell_replace_with(r) + s5_refcell_take(r) + s7_cell_replace(c) + s9_cell_take(c)
}
