#!/usr/bin/env python3
"""Verify the indexed-store experiment differs only in the selected method body."""
from pathlib import Path
import hashlib,re,json
here=Path(__file__).resolve().parent
candidate=(here/'input/field/wide_exact.rs').read_text()
original=(here/'source/original_wide_exact.rs').read_text()
pat=r'(?m)^    pub fn to_le_bytes\(self\) -> \[u8; Self::BYTE_LEN\] \{.*?^    \}'
cm=re.search(pat,candidate,re.S); om=re.search(pat,original,re.S)
assert cm and om and cm.start()==om.start()
assert hashlib.sha256(om.group(0).encode()).hexdigest()=='a54b5ffbd734cab9cbd0fc2b894a192e20ee816302589335291b9f836e0384f7'
assert candidate[:cm.start()]+om.group(0)+candidate[cm.end():] == original, 'non-method source difference'
b=cm.group(0)
assert b.count('to_le_bytes()')==8
assert all(f'bytes[{i}] = b{i//4}[{i%4}];' in b for i in range(32))
assert 'chunks_exact_mut' not in b and '.zip(' not in b and 'copy_from_slice' not in b
pins=json.loads((here/'source-pins.json').read_text())
assert hashlib.sha256(candidate.encode()).hexdigest()==pins['source_files']['cut_wide_exact_rs']['sha256']
print('PASS: only WideExact::to_le_bytes differs from pinned source; candidate has 8 limb conversions and 32 ordered explicit stores')
print('original_body_sha256='+hashlib.sha256(om.group(0).encode()).hexdigest())
print('candidate_body_sha256='+hashlib.sha256(b.encode()).hexdigest())
