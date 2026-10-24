#![allow(non_snake_case, unexpected_cfgs)]
use std::{alloc::Layout,mem::size_of,ptr::null_mut};
include!("Port22ARENA_selected.rs");

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(2)]
fn Port22ARENA_selected_alloc_frame() {
    use std::alloc::GlobalAlloc;
    // 256-byte arena with separate guard words, all bytes initialized.
    let mut backing: [usize;34] = kani::any();
    assert_eq!(size_of::<usize>(),8);
    let start = unsafe {backing.as_mut_ptr().add(1)} as usize;
    let offset: usize = kani::any();
    kani::assume(8 <= offset && offset <= 256);
    let first: bool = kani::any();
    let cursor = if first {0} else {start+offset};
    backing[1]=cursor;
    let x:usize=kani::any();
    kani::assume(x<34 && x!=1);
    let untouched=backing[x];
    let n:usize=kani::any();
    let a=if kani::any::<bool>() {4} else {8};
    // Invalid Layout is a rejected input, not an assumed allocator success.
    let Ok(layout)=Layout::from_size_align(n,a) else {return};
    if n==0 {return}; // GlobalAlloc requires nonzero size; fresh Vec n=0 skips allocate.
    let allocator=BumpAllocator{start,len:256};
    let initial=if cursor==0 {start+256} else {cursor};
    let candidate=initial.saturating_sub(n)& !(a.wrapping_sub(1));
    let result=unsafe {allocator.alloc(layout)};
    assert_eq!(backing[x],untouched);
    if candidate<start+8 {
        assert!(result.is_null());
        assert_eq!(backing[1],cursor);
    } else {
        assert_eq!(result as usize,candidate);
        assert_eq!(backing[1],candidate);
        assert_eq!(candidate%a,0);
        assert!(candidate+n<=initial);
    }
}
