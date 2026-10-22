#!/usr/bin/env python3
"""Frozen-release owner destruction has EMPTY byte write footprint.
Real full statement Box and Vec<u8> destructors execute via actual typed
std::ptr::drop_in_place. Only allocator deallocation is dispatched to actual
SDK BumpAllocator::dealloc as selected by frozen target_os=solana source.
No owner locals, allocations, account data or counters may be written. Fixture
covers all first reply lengths0..1769; owner validity and allocator dispatch
must come from the concrete admitted caller, not this host candidate alone.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-release-owner-drop.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();a=s.index('#[kani::requires(unsafe{(&*bytes).len()}==1768)]');b=s.index('unsafe fn frozen_release_dealloc',a)
s=s[:a]+'''#[kani::modifies()]
fn destroy_owners(statement:*mut Box<PoolV1PairForestTerminalStatementV1>,bytes:*mut Vec<u8>){
 unsafe{std::ptr::drop_in_place(bytes);std::ptr::drop_in_place(statement);}
}
'''+s[b:]
a=s.index('fn actual_owner_drop_frame(){');s=s[:a]+'''fn actual_owner_drop_frame(){
 let mut statement=std::mem::ManuallyDrop::new(Box::new(statement()));
 let reply:[u8;1769]=kani::any();let length:usize=kani::any();kani::assume(length<=1769);
 let mut bytes=std::mem::ManuallyDrop::new(reply[..length].to_vec());
 destroy_owners(&mut *statement,&mut *bytes);
 kani::cover!(length==0,"empty first output owner destruction is byte effect free");
 kani::cover!(length==1768,"accepted first output owner destruction is byte effect free");
 kani::cover!(length==1769,"oversized first output owner destruction is byte effect free");
}
}
'''
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('release-owner-drop-v1','release-owner-empty-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='All assertions/covers must pass. Frozen allocator dispatch/source/ABI, valid owner/caller and exact source destruction-order composition remain external. This candidate is a release-platform effect proof, not host System/free equivalence, full native-to-reference binding or whole S2.'),indent=2)+'\n')
