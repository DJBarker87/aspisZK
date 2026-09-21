#!/usr/bin/env python3
"""Compute one tensor child by multiplication and its complement by subtraction."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS, one_replace
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
assert not a.output.exists()
shutil.copytree(a.stage, a.output)
root = a.output / EXPERIMENTS
meta = json.loads((a.output / 'r17-sbf-probe.json').read_text())
path = root / 'r17_tensor_prefix.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == meta['tensor_prefix_sha256']
s = one_replace(before.decode(), '''//! Each leaf keeps the original multiplication order. No division, zero-case
//! exception, reassociation, or field-distributivity rewrite is needed.''', '''//! Complementary children use p*(1-z) = p-p*z. No division, new rejection,
//! data-dependent zero skipping, or new mask/challenge is introduced.''', 'accurate algebraic premise')
s = one_replace(s, '        let left_factor = K::ONE.sub(z);\n', '', 'remove redundant factor')
s = one_replace(s, '''            out[2 * i] = parent.mul(left_factor);
            out[2 * i + 1] = parent.mul(z);''', '''            let right = parent.mul(z);
            out[2 * i] = parent.sub(right);
            out[2 * i + 1] = right;''', 'share complementary product')
path.write_text(s)
meta['tensor_complement'] = {path.name: {'before_sha256': hashlib.sha256(before).hexdigest(),
    'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}}
gate = root / 'r17_tensor_check.rs'
s = one_replace(gate.read_text(), 'fn main() {', '''fn main() {
    let scale = sample(71);
    let mut tensor_out = vec![sample(999);1024];
    for bits in 0usize..1024 {
        let point = core::array::from_fn(|i| if bits & (1 << (9-i)) != 0 { K::ONE } else { K::ZERO });
        r17_tensor_prefix::fill(scale, &point, tensor_out.as_mut_slice().try_into().unwrap());
        for j in 0..1024 { assert_eq!(tensor_out[j], if j == bits {scale} else {K::ZERO}); }
    }
    println!("PASS: all 1024 Boolean tensor points x 1024 coordinates, scaled one-hot output");''', 'complete Boolean tensor control')
gate.write_text(s)
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
