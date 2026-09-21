#!/usr/bin/env python3
"""Instrument a fresh candidate stage without changing transcript/checks."""
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
meta = json.loads((a.output / 'r17-sbf-probe.json').read_text())
changes = {}

def mark(label):
    return '\n#[cfg(target_os="solana")] { solana_program::msg!("R17:' + label + '"); solana_program::log::sol_log_compute_units(); }\n'

def edit(name, transform):
    path = a.output / EXPERIMENTS / name
    before = path.read_bytes()
    after = transform(before.decode()).encode()
    path.write_bytes(after)
    changes[name] = {'before_sha256': hashlib.sha256(before).hexdigest(),
                     'after_sha256': hashlib.sha256(after).hexdigest()}

def verifier(s):
    # Both untyped and typed entrypoints keep their existing checkpoints.
    assert s.count('    checkpoint("v8:start");') == 2
    s = s.replace('    checkpoint("v8:start");', mark('entry') + '    checkpoint("v8:start");')
    assert s.count('    let s=semantic(w,binding,public,transition).map_err(|_|4u32)?;') == 2
    s = s.replace('    let s=semantic(w,binding,public,transition).map_err(|_|4u32)?;',
        mark('semantic-start') + '    let s=semantic(w,binding,public,transition).map_err(|_|4u32)?;' + mark('semantic-end'))
    assert s.count('    let prepared=crate::r17_relation::prepare(s,w).map_err(|_|5u32)?;') == 2
    s = s.replace('    let prepared=crate::r17_relation::prepare(s,w).map_err(|_|5u32)?;',
        '    let prepared=crate::r17_relation::prepare(s,w).map_err(|_|5u32)?;' + mark('prepare-end'))
    return s

def relation(s):
    s = one_replace(s, '    for channel in 0..2 {\n        let original =',
        '    for channel in 0..2 {' + mark('original-start') + '        let original =', 'channel start')
    s = one_replace(s, '        let dual = basis_transport::transport().dual(&original);',
        mark('original-end') + '        let dual = basis_transport::transport().dual(&original);' + mark('dual-end'), 'dual markers')
    return one_replace(s, '        ordinary[channel] = opening_weights::chord_transpose(&dual, abc);',
        '        ordinary[channel] = opening_weights::chord_transpose(&dual, abc);' + mark('chord-end'), 'chord marker')

edit('performance_verifier.rs', verifier)
edit('r17_host_relation.rs', relation)
meta['cu_profile'] = changes
meta['diagnostic_instrumentation'] = True
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
