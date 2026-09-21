#!/usr/bin/env python3
"""Replace SBF OnceLock/Vec map storage with immutable read-only arrays."""
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
metadata = json.loads((a.output / 'r17-sbf-probe.json').read_text())
path = a.output / EXPERIMENTS / 'r16_basis_transport.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == metadata['basis_specialization']['after_sha256']
s = before.decode()
s = one_replace(s, 'use std::sync::OnceLock;', '#[cfg(not(target_os="solana"))]\nuse std::sync::OnceLock;', 'host cache only')
for name, kind in [('order', 'usize'), ('inactive', 'bool')]:
    s = one_replace(s, f'    pub(crate) {name}: Vec<{kind}>,',
        f'    #[cfg(not(target_os="solana"))]\n    pub(crate) {name}: Vec<{kind}>,\n'
        f'    #[cfg(target_os="solana")]\n    pub(crate) {name}: [{kind}; N],', 'immutable SBF array')
s = one_replace(s, '''    #[cfg(target_os="solana")]
    pub fn new() -> Self {
        Self { order: fixed::ORDER.to_vec(), inactive: fixed::INACTIVE.to_vec() }
    }
''', '', 'no SBF heap constructor')
s = one_replace(s, "pub fn transport() -> &'static Transport {", '''#[cfg(target_os="solana")]
pub fn transport() -> &'static Transport {
    static T: Transport = Transport { order: fixed::ORDER, inactive: fixed::INACTIVE };
    &T
}
#[cfg(not(target_os="solana"))]
pub fn transport() -> &'static Transport {''', 'read-only SBF table')
path.write_text(s)
metadata['basis_specialization']['pre_static_sha256'] = hashlib.sha256(before).hexdigest()
metadata['basis_specialization']['after_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(metadata, indent=2) + '\n')
