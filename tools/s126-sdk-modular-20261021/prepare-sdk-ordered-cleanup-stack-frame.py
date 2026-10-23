#!/usr/bin/env python3
"""Keep the cleanup body, replace only harness payload Vecs by full stack arrays.
The SDK receives the SAME actual slice types/lengths, arbitrary bytes, metadata,
Rc/counter domain and actual guard types. Input Vec capacity was not SDK state;
its observation is removed. First-reply Vec and statement Box stay actual owners.
This avoids large proof-payload heap initialization under DFCC; not a source
implementation change or a smaller/zeroed SDK payload.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-ordered-cleanup-frame.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();original=s
needle=' let mut buffers=[kani::vec::exact_vec::<u8,58295>(),kani::vec::exact_vec::<u8,1880>(),kani::vec::exact_vec::<u8,1768>()];';assert s.count(needle)==1
s=s.replace(needle,''' let mut proof_bytes:[u8;58295]=kani::any();let mut public_bytes:[u8;1880]=kani::any();let mut checkpoint_bytes:[u8;1768]=kani::any();
 let mut buffers:[&mut[u8];3]=[&mut proof_bytes,&mut public_bytes,&mut checkpoint_bytes];''')
s=s.replace(' let capacities=core::array::from_fn::<_,3,_>(|i|buffers[i].capacity());\n','').replace('assert_eq!(buffers[i].capacity(),capacities[i]);','')
a=original.index('#[kani::requires(std::mem::size_of_val(&proof)');b=original.index('#[kani::proof_for_contract(ordered_cleanup)]',a)
assert original[a:b] in s
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('ordered-cleanup-frame-v1','ordered-cleanup-stack-frame-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),cleanup_source_sha256=hashlib.sha256(original[a:b].encode()).hexdigest(),qualification=__doc__,expected_time='Cached optimized compilation, then SAME cleanup full-heap frame on complete arbitrary58295/1880/1768-byte stack-backed SDK slices. Avoid large Vec-to-heap initialization under global DFCC instrumentation.8G cap unchanged.',remaining='Every property/cover must pass. SDK source/storage adequacy and matching leaf/tool/ABI pins remain; primitive source input is a borrowed slice, not its backing Vec. Explicit/compiler cleanup and frozen allocator/valid-owner/runtime transport, actual source call-site separation and oracle/TX2 joins remain. No whole S2.'),indent=2)+'\n')
