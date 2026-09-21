#!/usr/bin/env python3
"""Avoid unused reference storage on the non-reference path; retain both checks."""
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
assert hashlib.sha256(before).hexdigest() == meta['owned_weights'][path.name]['after_sha256']
s = one_replace(before.decode(), '''    let mut dense: [Vec<K>; 2] =
        core::array::from_fn(|c| (0..1024).map(|i| weights[c].weight_at(i)).collect());''',
'''    let mut dense: [Vec<K>; 2] = if reference {
        core::array::from_fn(|c| (0..1024).map(|i| weights[c].weight_at(i)).collect())
    } else { [Vec::new(), Vec::new()] };''', 'reference-only allocation')
def mark(label):
    return '\n    #[cfg(target_os="solana")] { solana_program::msg!("R17:' + label + '"); solana_program::log::sol_log_compute_units(); }\n'
for anchor, label in [
    ('    let first = compact(&w.v[417..423], claim);', 'dense-ready'),
    ('    let mut finals = [w.v[441..697].to_vec(), w.v[697..953].to_vec()];', 'first-fold-end'),
    ('    let (values, xs) = opened(w, &p, iv_g, &queries, a)?;', 'query-schedule-end'),
    ('    let inc = if reference {', 'openings-end'),
]:
    s = one_replace(s, anchor, mark(label) + anchor, label)
path.write_text(s)
meta['lazy_reference'] = {path.name: {'before_sha256': hashlib.sha256(before).hexdigest(),
                                   'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}}
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
