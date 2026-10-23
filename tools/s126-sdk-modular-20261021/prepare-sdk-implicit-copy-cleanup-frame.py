#!/usr/bin/env python3
"""Successful native post-first copy plus actual implicit typed cleanup.
Accepted-only tail: reply and checkpoint lengths1768. The separate native
accepted-context cut derives that length; this does not assume whole S2.
No explicit Drop, SDK/guard/copy model or verified callee stubs are used.
Frozen release deallocator dispatch remains an explicit qualified stub.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-implicit-cleanup-frame.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text()
s=s.replace('#[kani::modifies(counters[0].cast_mut()', '#[kani::requires(checkpoint.len()==1768)]\n#[kani::requires(destination==checkpoint.as_ptr().cast_mut().cast::<[u8;1768]>())]\n#[kani::modifies(destination,counters[0].cast_mut()',1)
needle='proof:std::cell::Ref<\'_,&mut[u8]>,reply:Vec<u8>)'
assert s.count(needle)==2
s=s.replace(needle,needle[:-1]+',destination:*mut[u8;1768])')
s=s.replace('implicit_cleanup(counters,checkpoint,public,statement,candidate,proof,reply);','implicit_cleanup(counters,checkpoint,public,statement,candidate,proof,reply,destination);')
s=s.replace('fn implicit_cleanup(counters:', 'fn implicit_cleanup(counters:').replace("checkpoint:std::cell::RefMut<'_,&mut[u8]>","mut checkpoint:std::cell::RefMut<'_,&mut[u8]>")
needle=' // Actual compiler implicit parameter cleanup, inside the checked wrapper.'
assert s.count(needle)==1
s=s.replace(needle,''' // This is the exact source copy operation on the native accepted length class.
 checkpoint.copy_from_slice(&reply);
'''+needle)
needle=' ordered_cleanup(counters,checkpoint_data,public_data,statement,candidate,proof_data,reply);'
assert s.count(needle)==1
s=s.replace(needle,''' let destination=checkpoint_data.as_mut_ptr().cast::<[u8;1768]>();
 ordered_cleanup(counters,checkpoint_data,public_data,statement,candidate,proof_data,reply,destination);''')
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('implicit-cleanup-frame-v2','implicit-copy-cleanup-frame-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,expected_time='Cached optimized compilation then actual constant-size native copy and implicit cleanup write-footprint, no nested contracts. Same6G/8G/Swap0.',remaining='Every property and cover must pass. Accepted-length cut, native implicit destruction order and call-site geometry must be concretely composed; general runtime/ABI/allocator and installed child/oracle/TX2 binding remain. No total-error-path or whole S2 claim.'),indent=2)+'\n')
