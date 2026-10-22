#!/usr/bin/env python3
"""Exact frozen allocator deallocation boundary, not a host-free substitute claim.
The wrapper executes real SDK BumpAllocator::dealloc selected by the frozen
program's target_os=solana global allocator. Its empty write frame is checked.
Allocation, owner-destructor dispatch and native/owned/runtime join remain.
"""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists();(O/'src').mkdir(parents=True)
s='''use solana_program::entrypoint::{BumpAllocator,HEAP_START_ADDRESS};
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
'''
(O/'src/lib.rs').write_text(s);(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-release-dealloc-v1"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
[profile.release]
opt-level=3
overflow-checks=true
''')
source=R/'programs/r1-cost-probe/src/lib.rs';text=source.read_text();a=text.index('#[cfg(target_os="solana")]');b=text.index('#[cfg(not(feature="no-entrypoint"))]',a)
(O/'release-allocator-selection.rs.txt').write_text(text[a:b]);(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),frozen_entrypoint_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),qualification=__doc__,scope='TOTAL deallocation operation for all valid Layout and arbitrary pointer bits; actual SDK empty body dereferences neither. No allocation or general valid-owner/runtime claim.'),indent=2)+'\n')
