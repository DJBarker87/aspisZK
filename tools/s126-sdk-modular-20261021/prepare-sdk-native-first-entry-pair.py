#!/usr/bin/env python3
"""Concrete native-to-reference FIRST-ENTRY implication, actual SDK methods.
The second execution is required only when native first is reached, the domain
needed by accepted-run callers. Both complete caller bodies, original SDK,
real guards, full typed statement and initial byte allocations are retained.
Fixes the demonstrated untagged-Option/observer codegen alias. Native/owned
first replies remain empty to isolate entry; no successful-tail theorem follows.
Frozen platform deallocation body is explicit, not a host-free equivalence.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-first-ordinary.py'),str(O),'native'],check=True)
p=O/'src/lib.rs';s=p.read_text();old='pub static mut s126_keep_coupled_cmp:Option<extern "C" fn(*const u8,*const u8,usize)->i32>=None;';assert s.count(old)==1
s=s.replace(old,'pub static mut s126_keep_coupled_cmp:GhostStorage<Option<extern "C" fn(*const u8,*const u8,usize)->i32>>=GhostStorage{value:None,allocation_tag:0x51a9000000000001};')
s=s.replace('s126_keep_coupled_cmp=Some(s126_coupled_cmp);','s126_keep_coupled_cmp.value=Some(s126_coupled_cmp);')
needle='if unsafe{CALLS.value[0][0]}==1 {';assert s.count(needle)==1;s=s.replace(needle,'if unsafe{CALLS.value[0]}==[1,1,1,1] {')
needle='#[kani::proof] #[kani::unwind(48)]';assert s.count(needle)==1
fn='''unsafe fn frozen_release_dealloc(pointer:*mut u8,layout:std::alloc::Layout){
 let allocator=solana_program::entrypoint::BumpAllocator{start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:256*1024};
 unsafe{std::alloc::GlobalAlloc::dealloc(&allocator,pointer,layout);}
}
'''
s=s.replace(needle,fn+'\n#[kani::stub(std::alloc::dealloc,frozen_release_dealloc)]\n'+needle)
s=s.replace('native and complete reference return the same exact first-prefix error','native reached first implies complete reference reached same first and exact empty-result length error')
assert '#[kani::stub(AccountInfo::' not in s
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('first-coupling-v3','first-entry-pair-v5'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,scope='Actual SDK caller control and same original fixed byte inputs/public semantic projection/k/None/common typed child order. Shared read-only scan/comparison ports consume previously checked concrete source leaves. Both whole callers execute on same original buffers; independent exact source entry+empty-finish+guard+release-owner frames must justify that reuse.',remaining='Every reachable assertion and covers must pass; instantiate existing source scan/gate and actual child interpretations, first-entry causality under arbitrary continuation, frozen allocator dispatch/runtime heap, and native returned-success/full-byte frame composition. This is a named native-to-reference prefix component, not complete stage1 or whole S2.'),indent=2)+'\n')
