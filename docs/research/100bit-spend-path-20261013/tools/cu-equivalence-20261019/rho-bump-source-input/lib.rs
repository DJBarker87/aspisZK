// Exact arithmetic of pinned BumpAllocator::alloc; pointer load/store exposed.
pub fn source_alloc(start:usize,len:usize,mut pos:usize,size:usize)->Option<usize> {
    if pos == 0 { pos = start + len; }
    pos = pos.saturating_sub(size);
    pos &= !(8usize.wrapping_sub(1));
    if pos < start + core::mem::size_of::<*mut u8>() { return None; }
    Some(pos)
}
