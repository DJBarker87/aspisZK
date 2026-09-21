#!/usr/bin/env python3
"""Retain output/scratch reuse; reject the measured batched-merge CU regression."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
assert not a.output.exists()
shutil.copytree(a.stage, a.output)
root = a.output / EXPERIMENTS
meta = json.loads((a.output / 'r17-sbf-probe.json').read_text())
path = root / 'r17_fast_g.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == meta['fast_g_reuse'][path.name]['after_sha256']
s = before.decode()
start = s.index('            for j in 0..end-start {')
end = s.index('\n        }\n        core::mem::swap', start)
s = s[:start] + '''            next[start..end].fill(K::ZERO);
            // Restore the original accumulation order while keeping owned buffers.
            for (from, to, other) in [(start, mid, node*2+1), (mid, end, node*2)] {
                let offset = DEN_OFFSETS[other];
                let count = DEN_LENGTHS[other];
                for i in from..to {
                    for k in 0..count {
                        let at = start + i - from + k;
                        next[at] = next[at].add(current[i].mul_m31(DENOMINATORS[offset+k]));
                    }
                }
            }''' + s[end:]
path.write_text(s)
meta['fast_g_reuse_only'] = {path.name: {
    'before_sha256': hashlib.sha256(before).hexdigest(),
    'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}}
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
