#!/usr/bin/env python3
"""Use short fixed-root convolutions only for fully balanced large numerator nodes."""
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
path = root / 'r17_fast_g.rs'
before = path.read_bytes()
assert hashlib.sha256(before).hexdigest() == meta['scalar_fma'][path.name]['after_sha256']
s = one_replace(before.decode(), '    assert_eq!(n, 2048);', '    assert!(matches!(n,64|128|256|2048));', 'transform lengths')
s = one_replace(s, 'let step = n / len;', 'let step = 2048 / len;', 'fixed master root stride')
s = one_replace(s, '(n - k * step) & (n - 1)', '(2048 - k * step) & 2047', 'inverse root stride')
s = one_replace(s, '        for x in a { *x = CM31::new(x.a.mul_pow2(20), x.b.mul_pow2(20)); }',
    '        let shift = (31-n.trailing_zeros()) as u8;\n        for x in a { *x = CM31::new(x.a.mul_pow2(shift), x.b.mul_pow2(shift)); }', 'inverse scale')
s = one_replace(s, 'fn numerator_into(coins: &[K; 271], out: &mut [K; 1024]) {',
    'include!("r17_hybrid_merge.rs");\n\nfn numerator_into(coins: &[K; 271], out: &mut [K; 1024], work: &mut [CM31]) {', 'shared workspace')
start = s.index('            next[start..end].fill(K::ZERO);')
end = s.index('\n        }\n        core::mem::swap', start)
s = s[:start] + '''            if matches!(size,64|128|256) && end-start==size {
                fft_merge(current,next,start,size,node,work);
            } else {
                scalar_merge(current,next,start,mid,end,node);
            }''' + s[end:]
s = one_replace(s, '    numerator_into(coins, out);', '    let mut work = vec![CM31::ZERO; 2048];\n    numerator_into(coins, out, &mut work);', 'reuse one buffer across tree and final FFT')
s = one_replace(s, '    let mut work = vec![CM31::ZERO; 2048];\n    for component', '    for component', 'remove later allocation')
s = one_replace(s, 'pub(super) fn check() {', 'pub(super) fn check() {\n    check_hybrid();', 'focused merge controls')
path.write_text(s)
meta['hybrid_merge'] = {path.name: {'before_sha256': hashlib.sha256(before).hexdigest(),
    'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}}
meta['hybrid_merge_files'] = {}
for name in ['r17_hybrid_merge.rs','r17_merge_generate.rs']:
    data = Path(__file__).with_name(name).read_bytes()
    (root/name).write_bytes(data)
    meta['hybrid_merge_files'][name] = hashlib.sha256(data).hexdigest()
manifest = root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text() + '\n[[bin]]\nname="r17-merge-generate"\npath="../r17_merge_generate.rs"\n')
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
