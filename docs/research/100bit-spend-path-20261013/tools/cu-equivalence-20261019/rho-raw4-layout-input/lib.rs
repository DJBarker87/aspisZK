#![feature(alloc_layout_extra)]
// Exact layout_array body on the actual residue element type; used only by
// the empty RawVec path. No replacement layout arithmetic or global allocator.
pub fn source_layout(cap:usize)->Option<(usize,usize)> {
    let elem_layout=core::alloc::Layout::new::<[u64;4]>();
    let layout=elem_layout.repeat_packed(cap).ok()?;
    Some((layout.size(),layout.align()))
}
