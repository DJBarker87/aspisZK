#!/usr/bin/env python3
"""Fresh staged SBF map specialization; preserve host constructor for checking."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil

from reconstruct_generated_inputs import EXPERIMENTS, one_replace

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage', type=Path, required=True)
p.add_argument('--table', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
assert not a.output.exists(), 'fresh destination required'
table = a.table.read_text()
m = re.fullmatch(r'pub const ORDER: \[usize; 1024\] = (\[[^\n]+\]);\n'
                 r'pub const INACTIVE: \[bool; 1024\] = (\[[^\n]+\]);\n', table)
assert m, 'expected exact exporter format'
order, inactive = map(json.loads, m.groups())
assert sorted(order) == list(range(1024)) and len(inactive) == 1024
assert all(type(v) is bool for v in inactive)
shutil.copytree(a.stage, a.output)
path = a.output / EXPERIMENTS / 'r16_basis_transport.rs'
before = path.read_bytes()
metadata = json.loads((a.output / 'r16-stage.json').read_text())
# Authenticate against the staged source manifest, not a regenerated inventory.
assert hashlib.sha256(before).hexdigest() == metadata['transport_sha256']
text = before.decode()
text = one_replace(text, 'use aspis_statement::pool_v1::{',
                   '#[cfg(not(target_os="solana"))]\nuse aspis_statement::pool_v1::{', 'host inventory import')
text = one_replace(text, '    pub fn new() -> Self {', '''    #[cfg(target_os="solana")]
    pub fn new() -> Self {
        Self { order: fixed::ORDER.to_vec(), inactive: fixed::INACTIVE.to_vec() }
    }
    #[cfg(not(target_os="solana"))]
    pub fn new() -> Self {''', 'SBF fixed map constructor')
text += '\nmod fixed { include!("r17_basis_tables.rs"); }\n'
path.write_text(text)
(path.parent / 'r17_basis_tables.rs').write_text(table)
exporter = path.parent / 'r17_export_basis.rs'
source = exporter.read_text()
source = one_replace(source, '    let map = basis::Transport::new();', '''    let map = basis::Transport::new();
    mod fixed { include!("r17_basis_tables.rs"); }
    assert_eq!(map.order.as_slice(), &fixed::ORDER);
    assert_eq!(map.inactive.as_slice(), &fixed::INACTIVE);''', 'source equality gate')
exporter.write_text(source)
probe = a.output / 'r17-sbf-probe.json'
state = json.loads(probe.read_text())
state['basis_specialization'] = {
    'before_sha256': hashlib.sha256(before).hexdigest(),
    'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    'table_sha256': hashlib.sha256(table.encode()).hexdigest(),
    'required_gate': 'run r17-export-basis in this stage before SBF build',
}
probe.write_text(json.dumps(state, indent=2) + '\n')
