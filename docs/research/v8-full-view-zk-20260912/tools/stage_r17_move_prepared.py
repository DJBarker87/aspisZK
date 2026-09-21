#!/usr/bin/env python3
"""Move consumed ordinary vectors into accumulators; no copied coefficient buffer."""
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
path = a.output / EXPERIMENTS / 'r17_host_relation.rs'
before = path.read_bytes()
meta = json.loads((a.output / 'r17-sbf-probe.json').read_text())
assert hashlib.sha256(before).hexdigest() == meta['lazy_reference'][path.name]['after_sha256']
s = one_replace(before.decode(), '''    let weights = core::array::from_fn(|channel| {
        let mut v = ordinary[channel].clone();''', '''    let [ordinary0, ordinary1] = ordinary;
    let weights = [(0, ordinary0), (1, ordinary1)].map(|(channel, mut v)| {''',
    'move each ordinary vector exactly once')
path.write_text(s)
meta['move_prepared'] = {path.name: {'before_sha256': hashlib.sha256(before).hexdigest(),
                                  'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}}
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
