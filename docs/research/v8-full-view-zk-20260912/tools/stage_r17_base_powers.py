#!/usr/bin/env python3
"""Specialize base-field node powers, preserving nodes, coins and summation order."""
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
path = root / 'r17_mask_workspace.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == meta['workspace_sha256']
s = before.decode()
s = one_replace(s, 'let node = K::from_cm31(CM31::from_m31(M31((i + 1) as u32)));',
                'let node = M31((i + 1) as u32);', 'same base-field node')
s = one_replace(s, 'let mut power = K::ONE;', 'let mut power = M31::ONE;', 'base-field power')
s = one_replace(s, 'weights[j].add(a.mul(power))', 'weights[j].add(a.mul_m31(power))', 'scalar extension scaling')
# power.mul(node) is now M31 multiplication; the recurrence and order are unchanged.
path.write_text(s)
meta['base_power_specialization'] = {'before_sha256': hashlib.sha256(before).hexdigest(),
                                    'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
meta['workspace_sha256'] = meta['base_power_specialization']['after_sha256']
gate = root / 'r17_tensor_check.rs'
s = gate.read_text()
s = one_replace(s, '        for structured in [false, true] {', '''
        assert_eq!(r17_structured_g::mask_weights(&point),
            r17_structured_g::mask_weights_reference(&point));
        for structured in [false, true] {''', 'retained QM31-power reference gate')
s = one_replace(s, '    println!("PASS: 6 cases x 2 channels x 1024 complete original-weight entries");',
    '    println!("PASS: 6 cases x 1024 G entries match retained QM31-power implementation");\n'
    '    println!("PASS: 6 cases x 2 channels x 1024 complete original-weight entries");', 'explicit G evidence')
gate.write_text(s)
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
