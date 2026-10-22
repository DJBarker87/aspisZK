#!/usr/bin/env python3
"""Actual compiler implicit cleanup in the native stage1 local destruction order.
No explicit Drop helper, ManuallyDrop or verified stub in the checked function.
Only explicit frozen release deallocator dispatch; runtime/ABI scope retained.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-ordered-cleanup-direct-frame.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();a=s.index('fn ordered_cleanup(');b=s.index('\n#[kani::proof_for_contract(ordered_cleanup)]',a)
signature="counters:[*const Cell<isize>;3],checkpoint:std::cell::RefMut<'_,&mut[u8]>,public:std::cell::Ref<'_,&mut[u8]>,statement:Box<PoolV1PairForestTerminalStatementV1>,candidate:[u8;688],proof:std::cell::Ref<'_,&mut[u8]>,reply:Vec<u8>"
s=s[:a]+('fn ordered_cleanup('+signature+') {\n implicit_cleanup(counters,checkpoint,public,statement,candidate,proof,reply);\n}\nfn implicit_cleanup('+signature+') {\n // Actual compiler implicit parameter cleanup, inside the checked wrapper.\n}\n')+s[b:]
s=s.replace('ordered_cleanup(proof_data,public_data,checkpoint_data,counters,statement,candidate,reply);','ordered_cleanup(counters,checkpoint_data,public_data,statement,candidate,proof_data,reply);')
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('ordered-cleanup-direct-frame-v1','implicit-cleanup-frame-v2'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,expected_time='Cached optimized compile then actual implicit destructor sequence DFCC counter-only check; no nested verified contracts or large copy.6G/8G/Swap0 unchanged.',remaining='All properties/covers must pass. The empty implicit callee is inside the DFCC wrapper: parameter destruction in a contracted function alone occurs after its ensures probe. Actual GOTO cleanup order must match frozen native order. General valid runtime heap/ABI/allocator interpretation, fixed-initial caller, concrete children/oracle/TX2 and S1/S6 remain. Not whole S2.'),indent=2)+'\n')
