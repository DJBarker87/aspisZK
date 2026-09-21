#!/usr/bin/env python3
"""Exact fixed Vandermonde table and four-product reduction; research only."""
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
prime = 2**31 - 1
assert 4 * (prime - 1)**2 < 2**64
# Column-major powers: the same nodes 1..271 and exponents 0..1023.
# These are public constants, not sampled masks or a replacement encoding.
rows = [[pow(i + 1, j, prime) for i in range(271)] for j in range(1024)]
table = root / 'r17_g_powers.rs'
table.write_text('static G_POWERS: [[u32; 271]; 1024] = [\n' +
    ''.join('[' + ','.join(map(str, row)) + '],\n' for row in rows) + '];\n')
s = before.decode()
start = s.index('    let mut j = 0;\n    while j < N {')
assert s[start:].endswith('}\n')
s = s[:start] + '''    // Coin weights are canonical outputs of field operations above.
    // Four products are < 2^64. Reduction occurs before adding a fifth.
    for j in 0..N {
        let mut out = [M31::ZERO; 4];
        let mut i = 0;
        while i < COINS {
            let mut sums = [0u64; 4];
            let end = core::cmp::min(i + 4, COINS);
            while i < end {
                let a = coin_weights[i];
                let b = G_POWERS[j][i] as u64;
                sums[0] += a.c0.a.0 as u64 * b;
                sums[1] += a.c0.b.0 as u64 * b;
                sums[2] += a.c1.a.0 as u64 * b;
                sums[3] += a.c1.b.0 as u64 * b;
                i += 1;
            }
            for k in 0..4 { out[k] = out[k].add(M31::reduce_u64(sums[k])); }
        }
        weights[j] = K { c0: CM31::new(out[0], out[1]), c1: CM31::new(out[2], out[3]) };
    }
}

include!("r17_g_powers.rs");

#[cfg(not(performance_sbf))]
pub(super) fn check_fixed_table() {
    for i in 0..COINS {
        let node = M31((i + 1) as u32);
        let mut power = M31::ONE;
        for j in 0..N {
            assert_eq!(G_POWERS[j][i], power.0);
            power = power.mul(node);
        }
    }
    let p = super::corelib::field::P as u64;
    let maximal = 4 * (p - 1) * (p - 1);
    assert_eq!(M31::reduce_u64(maximal).0, 4);
}
'''
path.write_text(s)
meta['fixed_g_table'] = {
    'before_sha256': hashlib.sha256(before).hexdigest(),
    'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    'table_sha256': hashlib.sha256(table.read_bytes()).hexdigest(),
    'entries': 271 * 1024,
    'canonical_four_product_bound': str(4 * (prime - 1)**2),
}
meta['workspace_sha256'] = meta['fixed_g_table']['after_sha256']
gate = root / 'r17_tensor_check.rs'
t = one_replace(gate.read_text(), 'fn main() {', '''fn main() {
    r17_mask_workspace::check_fixed_table();
    println!("PASS: all 277504 fixed powers equal source M31 recurrence; maximal four-product reduction");''', 'fixed table source gate')
gate.write_text(t)
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
