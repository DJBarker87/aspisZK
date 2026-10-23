use solana_program::entrypoint::{BumpAllocator,HEAP_START_ADDRESS};
use std::alloc::{GlobalAlloc,Layout};
const RELEASE:BumpAllocator=BumpAllocator{start:HEAP_START_ADDRESS as usize,len:256*1024};
#[kani::modifies()]
fn release_dealloc(pointer:*mut u8,layout:Layout){
 unsafe{<BumpAllocator as GlobalAlloc>::dealloc(&RELEASE,pointer,layout);}
}
#[kani::proof_for_contract(release_dealloc)]
fn actual_release_dealloc_frame(){
 let address:usize=kani::any();let size:usize=kani::any();let align:usize=kani::any();
 let layout=Layout::from_size_align(size,align);if let Ok(layout)=layout {
  release_dealloc(address as *mut u8,layout);
  kani::cover!(address==0,"frozen dealloc does not inspect null pointer");
  kani::cover!(address==usize::MAX,"frozen dealloc does not inspect arbitrary address");
 }
}
