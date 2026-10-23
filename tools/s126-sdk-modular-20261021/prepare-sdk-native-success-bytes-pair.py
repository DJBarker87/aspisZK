#!/usr/bin/env python3
"""Complete native/reference success with UNSEEDED original byte inputs.
Only the source-reached control/metadata conditions are retained. Proof prefix,
tag, public and checkpoint bytes are fully arbitrary; no byte initialization or
zero-checkpoint premise. The reference receives a real clone of the original
checkpoint bytes taken before the native write, plus original proof/public
allocations. Native/source scans and comparisons are coupled pure ports;
actual source interpretations, control-class and runtime/oracle joins remain.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-success-image-pair.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text()
needle=' unsafe{std::ptr::copy_nonoverlapping(plan().candidate.as_ptr(),buffers[0].as_mut_ptr(),688);}\n buffers[0][696]=2;';assert s.count(needle)==1;s=s.replace(needle,'')
s=s.replace('vec![0;1768]','kani::vec::exact_vec::<u8,1768>()',1)
s=s.replace('different:false','different:kani::any()')
needle=' let actual={';assert s.count(needle)==1;s=s.replace(needle,' let mut checkpoint_initial=Some(buffers[2].clone());\n'+needle)
needle='bytes:if i==2 {vec![0;1768]}else{bytes}';assert s.count(needle)==1;s=s.replace(needle,'bytes:if i==2 {checkpoint_initial.take().unwrap()}else{bytes}')
# This cut is the actual accepted-event implication, not an assumed reference run.
needle=' // Native handles are gone.';assert s.count(needle)==1
s=s.replace(needle,' assert!(!actual.is_ok()||unsafe{CALLS.value[0]}==[1,1,1,1],"actual complete native acceptance derives its reached first prefix");\n'+needle)
assert 'buffers[0][696]=2' not in s and 'vec![0;1768]' not in s
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('success-image-pair-v1','success-bytes-pair-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,expected_time='Cached optimized compilation, actual successful SDK/native-reference paired execution with original copy/implicit cleanup; seed deletion reduces the earlier copy graph rather than increasing caps.',remaining='Every assertion/cover must pass. Source accepted control-class completeness, pure decoder/validator/encoder/first and scan/comparison interpretation, same original proof/public frame, valid runtime/heap/allocator/ABI/oracle and cross-TX transport remain. No seeded-byte premise remains in this candidate. No whole S2 claim.'),indent=2)+'\n')
