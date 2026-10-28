#![feature(alloc_layout_extra)]
use std::alloc::{Layout, LayoutError};
// Owned before-body: propagate the existing zero-data LayoutError instead of
// constructing its private std field. No allocator or pointer is evaluated.
fn historical(layout: Layout, n: usize) -> Result<(Layout, usize), LayoutError> {
    let padded = layout.pad_to_align();
    let result = if let Some(k) = n.checked_sub(1) {
        padded.repeat_packed(k)?.extend_packed(layout)?
    } else { layout.repeat_packed(0)? };
    Ok((result, padded.size()))
}
fn main() {
    let unpadded = Layout::from_size_align(1, 8).unwrap();
    let before = historical(unpadded, 1).unwrap();
    let after = unpadded.repeat(1).unwrap();
    assert_eq!((before.0.size(), before.0.align(), before.1), (1, 8, 8));
    assert_eq!((after.0.size(), after.0.align(), after.1), (8, 8, 8));
    let padded = Layout::from_size_align(8, 8).unwrap();
    for n in [0,1,2,1024,usize::MAX] {
        let old = historical(padded,n).map(|(p,s)|(p.size(),p.align(),s));
        let new = padded.repeat(n).map(|(p,s)|(p.size(),p.align(),s));
        assert_eq!(old,new);
    }
    let zst = Layout::from_size_align(0,8).unwrap();
    assert_eq!(historical(zst,usize::MAX).unwrap().0.size(),0);
    assert_eq!(zst.repeat(usize::MAX).unwrap().0.size(),0);
    println!("PASS unpadded before(size1,align8,stride8) after(size8,align8,stride8); padded success/error cases and zero-sized repeat agree. This is outside real-type RawVec layouts; finite validation only.");
}
