#!/usr/bin/env python3
"""Fresh ownership-reuse candidate, retaining old borrowed references."""
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
changes = {}
def edit(name, transform):
    path = root / name
    before = path.read_bytes()
    path.write_text(transform(before.decode()))
    changes[name] = {'before_sha256': hashlib.sha256(before).hexdigest(),
                     'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
edit('relation_callback.rs', lambda s: one_replace(s, 'mod r17_tensor_prefix;',
    'mod r17_tensor_prefix;\nmod r17_owned_weights;', 'owned weight module'))
def relation(s):
    s = one_replace(s, 'let dual = basis_transport::transport().dual(&original);',
                    'let dual = crate::r17_owned_weights::dual(original);', 'owned dual')
    return one_replace(s, 'opening_weights::chord_transpose(&dual, abc)',
                       'crate::r17_owned_weights::chord(dual, abc)', 'owned chord')
edit('r17_host_relation.rs', relation)
data = Path(__file__).with_name('r17_owned_weights.rs').read_bytes()
(root / 'r17_owned_weights.rs').write_bytes(data)
gate = root / 'r17_tensor_check.rs'
s = one_replace(gate.read_text(), 'mod r17_tensor_prefix;',
                'mod r17_tensor_prefix;\nmod r17_owned_weights;', 'gate owned module')
s = one_replace(s, 'fn main() {', '''fn main() {
    for case in 0..20 {
        let values: Vec<_> = (0..1024).map(|j| if case == 0 { K::ZERO }
            else { sample(case * 1024 + j) }).collect();
        let expected = basis_transport::transport().dual(&values);
        let actual = r17_owned_weights::dual(values);
        assert_eq!(actual, expected);
        let abc = [sample(case * 3), sample(case * 3 + 1), sample(case * 3 + 2)];
        assert_eq!(r17_owned_weights::chord(actual, abc),
            r17_opening_weights::chord_transpose(&expected, abc));
    }
    println!("PASS: 20 cases x 1024 owned dual and chord entries match references");
''', 'ownership differential gate')
gate.write_text(s)
meta['owned_weights'] = changes
meta['owned_weights_sha256'] = hashlib.sha256(data).hexdigest()
meta['callback_after_sha256'] = changes['relation_callback.rs']['after_sha256']
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
