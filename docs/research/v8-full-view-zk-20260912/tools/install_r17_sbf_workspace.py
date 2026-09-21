#!/usr/bin/env python3
"""Route a fresh research stage through heap-backed caller-owned mask buffers."""
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
metadata = json.loads((a.output / 'r17-sbf-probe.json').read_text())
changes = {}

def edit(name, transform):
    path = root / name
    before = path.read_bytes()
    after = transform(before.decode()).encode()
    path.write_bytes(after)
    changes[name] = {'before_sha256': hashlib.sha256(before).hexdigest(),
                     'after_sha256': hashlib.sha256(after).hexdigest()}

edit('relation_callback.rs', lambda s: one_replace(s, 'mod r17_structured_g;',
    'mod r17_structured_g;\nmod r17_mask_workspace;', 'workspace module'))
edit('r17_structured_g.rs', lambda s: one_replace(s,
    'pub(super) fn mask_weights(point: &[K; ROUNDS]) -> Vec<K> {', '''
pub(super) fn mask_weights(point: &[K; ROUNDS]) -> Vec<K> {
    // Vec fills heap storage directly; do not materialize large stack arrays.
    let mut coins = vec![K::ZERO; COINS];
    let mut weights = vec![K::ZERO; N];
    super::r17_mask_workspace::mask_weights_into(point,
        coins.as_mut_slice().try_into().unwrap(),
        weights.as_mut_slice().try_into().unwrap());
    weights
}
#[cfg(not(target_os="solana"))]
pub(super) fn mask_weights_reference(point: &[K; ROUNDS]) -> Vec<K> {''', 'heap workspace adapter') + '''
#[test]
fn r17_workspace_adapter_matches_reference() {
    for case in 0..16usize {
        let point = core::array::from_fn(|i| scalar(1 + case * 11 + i));
        assert_eq!(mask_weights(&point), mask_weights_reference(&point));
    }
}
''')
workspace = Path(__file__).with_name('r17_mask_workspace.rs').read_bytes()
(root / 'r17_mask_workspace.rs').write_bytes(workspace)
metadata['callback_after_sha256'] = changes['relation_callback.rs']['after_sha256']
metadata['workspace_adapter'] = changes
metadata['workspace_sha256'] = hashlib.sha256(workspace).hexdigest()
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(metadata, indent=2) + '\n')
