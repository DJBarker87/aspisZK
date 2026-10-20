#!/usr/bin/env python3
from pathlib import Path
import hashlib,re
p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b.encode() if isinstance(b,str) else b).hexdigest()
original=(p/'candidate/original_wide_exact.rs').read_text()
candidate=(p/'candidate/field/wide_exact.rs').read_text()
pat=r'(?m)^    pub fn to_le_bytes\(self\) -> \[u8; Self::BYTE_LEN\] \{.*?^    \}'
om=re.search(pat,original,re.S); cm=re.search(pat,candidate,re.S)
assert om and cm and om.start()==cm.start()
assert sha(om.group())=='a54b5ffbd734cab9cbd0fc2b894a192e20ee816302589335291b9f836e0384f7'
assert candidate[:cm.start()]+om.group()+candidate[cm.end():]==original
body=cm.group()
assert body.count('to_le_bytes()')==8
assert all(f'bytes[{i}] = b{i//4}[{i%4}];' in body for i in range(32))
assert 'chunks_exact_mut' not in body and '.zip(' not in body and 'copy_from_slice' not in body
raw=(p/'candidate/generated/Funs.lean').read_text()
opts='set_option maxHeartbeats 1000000\n\n/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/\nset_option maxRecDepth 2048\n\n'
assert raw.count(opts)==1
clean=(p/'source-adapter/FunsNoResourceOptions.lean').read_text()
assert clean==raw.replace(opts,'')
proof=(p/'lean/ToBytesGeneratedOutputV11.lean').read_text()
assert 'indexed_candidate_to_le_bytes' in proof and 'expectedBytes' in proof
print('PASS candidate diff: only WideExact::to_le_bytes changed; 8 conversions + 32 ordered stores')
print('PASS Lean adapter: exact emitted Funs after removing only the two resource option declarations')
print('original_method_sha256='+sha(om.group()))
print('candidate_method_sha256='+sha(body))
print('generated_funs_sha256='+sha(raw.encode()))
print('clean_adapter_sha256='+sha(clean.encode()))
