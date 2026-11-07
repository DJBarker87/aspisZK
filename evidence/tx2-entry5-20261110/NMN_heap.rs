// cfg(kani)-only typed allocation channel experiment. No global mutable record.
// The allocator value is stateless; all owner cells belong to fresh allocations.
use core::alloc::{GlobalAlloc,Layout};
#[repr(C)]
struct NMN_Header { owner:UnsafeCell<*mut ()> }
struct NMN_Allocator;
unsafe impl GlobalAlloc for NMN_Allocator {
 unsafe fn alloc(&self,layout:Layout)->*mut u8 {
  let align=core::cmp::max(layout.align(),16);
  let Some(size)=layout.size().checked_add(align) else{return core::ptr::null_mut()};
  let Ok(total)=Layout::from_size_align(size,align) else{return core::ptr::null_mut()};
  let raw=unsafe{std::alloc::System.alloc(total)};
  if raw.is_null(){return raw;}
  let data=unsafe{raw.add(align)};
  let h=unsafe{data.sub(core::mem::size_of::<NMN_Header>()).cast::<NMN_Header>()};
  unsafe{h.write(NMN_Header{owner:UnsafeCell::new(core::ptr::null_mut())});}
  data
 }
 unsafe fn dealloc(&self,_p:*mut u8,_layout:Layout) {
  // Retained until scope exit so LOCAL instrumentation survives owned drops.
  // No account/return-data effect or allocator reclamation is claimed.
 }
}
#[global_allocator]
static NMN_ALLOCATOR:NMN_Allocator=NMN_Allocator;
unsafe fn NMN_header(p:*const u8)->*const NMN_Header {
 unsafe{p.sub(core::mem::size_of::<NMN_Header>()).cast()}
}
unsafe fn NMN_set_owner(p:*const u8,owner:*mut ()){
 unsafe{*(*NMN_header(p)).owner.get()=owner;}
}
unsafe fn NMN_owner(p:*const u8)->*mut () {
 unsafe{*(*NMN_header(p)).owner.get()}
}
