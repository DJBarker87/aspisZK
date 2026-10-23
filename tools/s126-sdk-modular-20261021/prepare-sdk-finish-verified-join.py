#!/usr/bin/env python3
"""Exact native post-child copy/drop versus full owned heap using a proved std
primitive. The reached descriptor normalization and prior caller are explicit
remaining transports; no complete stage1 or release result is inferred.
"""
from pathlib import Path
import tempfile,subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);T=R/'tools/s126-sdk-modular-20261021'
subprocess.run(['python3',str(T/'prepare-sdk-finish-join.py'),str(O),'normalized'],check=True)
p=O/'src/lib.rs';s=p.read_text()
s=s.replace('let mut b1:[u8;58295]','let mut b1:[u8;1880]').replace('let mut b2:[u8;58295]','let mut b2:[u8;1768]')
with tempfile.TemporaryDirectory() as d:
 subprocess.run(['python3',str(T/'prepare-sdk-std-copy-frame.py'),d],check=True)
 primitive=(Path(d)/'src/lib.rs').read_text();a=primitive.index(' static mut OBSERVED:usize=0;');b=primitive.index(' #[kani::proof] #[kani::unwind(8)]',a);definitions=primitive[a:b]
s=s.replace('use super::*;\n','use super::*;\n'+definitions+'\n',1)
s=s.replace('#[kani::proof] #[kani::unwind(40)]','#[kani::stub(<[u8]>::copy_from_slice,copy_bridge)]\n#[kani::stub_verified(verified_byte_copy)]\n#[kani::proof] #[kani::unwind(40)]')
observation=' let observed_slot:usize=kani::any();kani::assume(observed_slot<3);\n let observed:usize=kani::any();kani::assume(observed<lengths[observed_slot]);\n'
s=s.replace(' let mut expected_trace=Vec::new();',observation+' let copy_index=if observed_slot==2 {observed}else{0};\n unsafe{OBSERVED=copy_index;EXPECTED=reply_bytes[copy_index];}\n let mut expected_trace=Vec::new();')
s=s.replace(' let observed_slot:usize=kani::any();kani::assume(observed_slot<3);\n if lengths[observed_slot]>0 {\n  let observed:usize=kani::any();kani::assume(observed<lengths[observed_slot]);',' if lengths[observed_slot]>0 {')
p.write_text(s)
c=O/'Cargo.toml';c.write_text(c.read_text().replace('aspis-s126-sdk-finish-join','aspis-s126-sdk-finish-verified-join'))
m=json.loads((O/'source-cut.json').read_text());sha=lambda x:hashlib.sha256(x.encode()).hexdigest()
m.update(source_sha256=sha(s),qualification=__doc__,std_copy_definitions_sha256=sha(definitions),std_copy_primitive_source_sha256=sha(primitive),std_copy_leaf_proof='sdk-std-copy-frame-join-v1',std_copy_bridge_proof='sdk-std-copy-bridge-join-v1',domain='Actual SDK accounts/full owned heap with exact58295/1880/1768 buffers, all contents, distinct data identities and independent lamport alias maps, all signed data/lamport counters, metadata and actual Rc headers. Every reply length0..1769/all bytes; all ordinary statuses, acquisition traces, guard drops and arbitrary byte in any actual root are compared. The specialized copy preconditions must be checked at actual calls. Frozen native finish block is unchanged. Earlier source normalization/children and runtime heap embedding remain explicit.')
(O/'source-cut.json').write_text(json.dumps(m,indent=2)+'\n')
