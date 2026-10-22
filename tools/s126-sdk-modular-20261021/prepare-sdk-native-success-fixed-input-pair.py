#!/usr/bin/env python3
"""Unseeded complete successful pair tied to FIXED INITIAL proof/public bytes.
Two independent symbolic coordinates span the entire58295-byte proof account
and1880-byte public account. Both actual first sites and post-native buffers
must equal their original input bytes. No independent input-frame premise.
Original SDK/copy/implicit cleanup, full statement, arbitrary common checkpoint,
original checkpoint clone and source-reached control class are retained.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-success-bytes-pair.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();needle='fn plan()->';a=s.index(needle)
s=s[:a]+'''static mut ORIGINAL_INPUT_INDICES:GhostStorage<[usize;2]>=GhostStorage{value:[0;2],allocation_tag:0x51b1000000000001};
static mut ORIGINAL_INPUT_BYTES:GhostStorage<[u8;2]>=GhostStorage{value:[0;2],allocation_tag:0x51b1000000000002};
'''+s[a:]
needle=' let expected_public=unsafe{NATIVE_ROOT_PTRS.value[1]};';assert s.count(needle)==1
s=s.replace(needle,needle+'''
 let input_indices=unsafe{ORIGINAL_INPUT_INDICES.value};let input_bytes=unsafe{ORIGINAL_INPUT_BYTES.value};
 assert_eq!(bytes[input_indices[1]],input_bytes[1],"each actual first uses the fixed ORIGINAL public byte at every coordinate");
 assert_eq!(unsafe{NATIVE_ROOT_PTRS.value[0].add(input_indices[0]).read()},input_bytes[0],"each actual first uses the fixed ORIGINAL full proof-account byte at every coordinate");
''')
needle=' let checkpoint_index:usize=kani::any();kani::assume(checkpoint_index<1768);';assert s.count(needle)==1
s=s.replace(needle,needle+'''
 let original_proof_index:usize=kani::any();kani::assume(original_proof_index<58295);
 let original_public_index:usize=kani::any();kani::assume(original_public_index<1880);
 let original_proof_byte=buffers[0][original_proof_index];let original_public_byte=buffers[1][original_public_index];
 unsafe{ORIGINAL_INPUT_INDICES.value=[original_proof_index,original_public_index];ORIGINAL_INPUT_BYTES.value=[original_proof_byte,original_public_byte];}
''')
needle=' assert_eq!(amounts,initial_amounts);';assert s.count(needle)==1
s=s.replace(needle,needle+'''
 assert_eq!(buffers[0][original_proof_index],original_proof_byte,"complete native caller preserves every ORIGINAL proof-account byte");
 assert_eq!(buffers[1][original_public_index],original_public_byte,"complete native caller preserves every ORIGINAL public-account byte");
''')
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('success-bytes-pair-v1','success-fixed-input-pair-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,expected_time='Cached optimized compilation then enclosing unseeded successful native/reference pair with full-range input-frame coordinates, added to the green123.508s predecessor. No cap increase.',remaining='All assertion/cover inventory must pass. Source control-class completeness and pure-child/scan/comparison interpretation, valid runtime/heap/ABI/allocator/oracle and cross-TX binding remain. No original-byte frame is assumed. No full S2/TOTAL-stage claim.'),indent=2)+'\n')
