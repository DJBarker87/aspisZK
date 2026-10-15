#!/usr/bin/env python3
from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
orig=(root/'baseline/field/wide_exact.rs').read_text()
cand=(root/'input/field/wide_exact.rs').read_text()
old_guard='        if limbs.iter().any(|&limb| limb >= P) {\n            return None;\n        }'
new_guard='        if limbs[0] >= P || limbs[1] >= P || limbs[2] >= P || limbs[3] >= P\n            || limbs[4] >= P || limbs[5] >= P || limbs[6] >= P || limbs[7] >= P {\n            return None;\n        }'
old_parse='        let bytes: &[u8; Self::BYTE_LEN] = bytes.try_into().ok()?;\n        let mut limbs = [0; Self::LIMB_COUNT];\n        for (limb, chunk) in limbs.iter_mut().zip(bytes.chunks_exact(4)) {\n            *limb = u32::from_le_bytes(chunk.try_into().ok()?);\n        }'
new_parse='        if bytes.len() != Self::BYTE_LEN {\n            return None;\n        }\n        let limbs = [\n            u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]),\n            u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]),\n            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),\n            u32::from_le_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]),\n            u32::from_le_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]),\n            u32::from_le_bytes([bytes[20], bytes[21], bytes[22], bytes[23]]),\n            u32::from_le_bytes([bytes[24], bytes[25], bytes[26], bytes[27]]),\n            u32::from_le_bytes([bytes[28], bytes[29], bytes[30], bytes[31]]),\n        ];'
assert orig.count(old_guard)==1 and orig.count(old_parse)==1
expected=orig.replace(old_guard,new_guard,1).replace(old_parse,new_parse,1)
assert cand==expected, 'candidate differs outside the two authorized bodies'
assert sha(root/'input/field.rs')=='28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea'
assert sha(root/'input/field/wide_exact.rs')=='6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b'
assert sha(root/'attempt-h2/source/field.rs')==sha(root/'input/field.rs')
assert sha(root/'attempt-h2/source/field/wide_exact.rs')==sha(root/'input/field/wide_exact.rs')
assert sha(root/'attempt-h/source/field/wide_exact.rs')=='c8d01761f5f1ae8749252655752c7ea156fb442bca4e07c97aa25acf76df9410'
translation=json.loads((root/'attempt-h2/generated/translation.json').read_text())
assert len(translation['functions'])==3 and all(not f['is_opaque'] for f in translation['functions'])
print('PASS: only the exact from_limbs guard and from_le_bytes body differ; h2 source pins match; 3 translated functions are nonopaque')
