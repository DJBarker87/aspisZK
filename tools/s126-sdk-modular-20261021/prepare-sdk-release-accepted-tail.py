#!/usr/bin/env python3
"""ACCEPTED-ONLY native post-first whole write-frame with frozen deallocation.
Original SDK acquisitions, full statement Box/candidate and original guard/owner
ordering retained. The accepted source finish has first_ok and reply_len1768;
other returned images are covered by the existing exact native finish checks.
std::alloc::dealloc delegates to the actual frozen SDK BumpAllocator body.
This is an explicit host/release-allocator proof candidate, not runtime dispatch
or child/source installation by itself. No safety assertions disabled.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-tail-write-frame.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();s=s.replace('#[kani::requires(reply_len<=1769)]','#[kani::requires(reply_len==1768 && first_ok)]')
s=s.replace('kani::assume(reply_len<=1769);let first_ok:bool=kani::any();','kani::assume(reply_len==1768);let first_ok:bool=true;')
needle='#[kani::proof_for_contract(native_tail_frame)]';assert s.count(needle)==1
fn='''unsafe fn frozen_release_dealloc(pointer:*mut u8,layout:std::alloc::Layout){
 let allocator=solana_program::entrypoint::BumpAllocator{start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:256*1024};
 unsafe{std::alloc::GlobalAlloc::dealloc(&allocator,pointer,layout);}
}
'''
s=s.replace(needle,fn+'\n#[kani::stub(std::alloc::dealloc,frozen_release_dealloc)]\n'+needle)
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('native-tail-write-frame-v4','release-accepted-tail-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='All frame and safety checks must pass; then supply frozen allocator dispatch/heap abstraction and compose native entry/accepted finish facts and exact installed children. No whole source/S2, TOTAL or soundness claim from this candidate alone.'),indent=2)+'\n')
