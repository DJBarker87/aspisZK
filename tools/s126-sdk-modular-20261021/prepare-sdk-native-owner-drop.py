#!/usr/bin/env python3
"""Successful-path actual Box/Vec owner destruction frame, full statement type.
Actual compiler-style drop_in_place entrypoints take typed owner pointers;
only their two owner locals and two owned allocations may be modified or freed.
Fixture ManuallyDrop prevents a second destruction after the checked operation.
No SDK/Drop stubs. Full Box/Vec owners are retained.
Together with guard/copy frames this isolates the previously timed-out tail.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-tail.py'),str(O),'2'],check=True)
p=O/'src/lib.rs';s=p.read_text();a=s.index('#[cfg(kani)] mod proofs');head=s[:a];a=s.index('fn statement()->',a);b=s.index('#[kani::proof]',a);statement=s[a:b]
s=head+'''#[cfg(kani)] mod proofs {
use super::*;
'''+statement+'''
#[kani::requires(unsafe{(&*bytes).len()}==1768)]
#[kani::requires(statement_pointer==unsafe{(&**statement as *const PoolV1PairForestTerminalStatementV1).cast_mut()})]
#[kani::requires(bytes_pointer==unsafe{(&*bytes).as_ptr().cast_mut().cast::<[u8;1768]>()})]
#[kani::modifies(statement,bytes,statement_pointer,bytes_pointer)]
fn destroy_owners(statement:*mut Box<PoolV1PairForestTerminalStatementV1>,bytes:*mut Vec<u8>,statement_pointer:*mut PoolV1PairForestTerminalStatementV1,bytes_pointer:*mut[u8;1768]){
 unsafe{std::ptr::drop_in_place(bytes);std::ptr::drop_in_place(statement);}
}
#[kani::proof_for_contract(destroy_owners)] #[kani::unwind(48)]
fn actual_owner_drop_frame(){
 let mut statement=std::mem::ManuallyDrop::new(Box::new(statement()));let mut bytes=std::mem::ManuallyDrop::new(kani::vec::exact_vec::<u8,1768>());
 let statement_pointer=(&**statement as *const PoolV1PairForestTerminalStatementV1).cast_mut();let bytes_pointer=bytes.as_ptr().cast_mut().cast::<[u8;1768]>();
 destroy_owners(&mut *statement,&mut *bytes,statement_pointer,bytes_pointer);
 kani::cover!(true,"actual full statement and checkpoint byte owners destroyed");
}
}
'''
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('native-post-first-tail-root2-v5','native-owner-drop-v3'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='All properties/cover must pass; instantiate owned allocation separation in actual native continuation, account for frozen allocator/runtime, and compose exact order with copy/guard leaves. No whole S2.'),indent=2)+'\n')
