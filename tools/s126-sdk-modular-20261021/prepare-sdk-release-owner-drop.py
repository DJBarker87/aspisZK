#!/usr/bin/env python3
"""Owner drop with frozen release deallocation semantics explicitly supplied.
This is an isolated host proof candidate: std::alloc::dealloc is replaced by a
wrapper executing actual SDK BumpAllocator::dealloc, selected in frozen Solana
source. It is not a proof of host System/free, allocator dispatch, allocation
or full runtime/source transport. No safety properties are disabled.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-owner-drop.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();needle='#[kani::proof_for_contract(destroy_owners)]';assert s.count(needle)==1
fn='''unsafe fn frozen_release_dealloc(pointer:*mut u8,layout:std::alloc::Layout){
 let allocator=solana_program::entrypoint::BumpAllocator{start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:256*1024};
 unsafe{std::alloc::GlobalAlloc::dealloc(&allocator,pointer,layout);}
}
'''
s=s.replace(needle,fn+'\n#[kani::stub(std::alloc::dealloc,frozen_release_dealloc)]\n'+needle);p.write_text(s)
p=O/'Cargo.toml';p.write_text(p.read_text().replace('native-owner-drop-v3','release-owner-drop-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='All properties/cover must pass; validate exact std dealloc dispatch and frozen BumpAllocator source/ABI selection before source adoption. Then instantiate valid owner allocation/caller separation and compose copy/guard/owner effects; SDK/native/reference/runtime/child/oracle/TX2 join remains. No source closure from this candidate alone.'),indent=2)+'\n')
