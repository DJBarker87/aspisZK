#!/usr/bin/env python3
"""Stage the exact-map product-tree/CM31 convolution experiment."""
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
start = s.index('    // Coin weights are canonical outputs')
end = s.index('\n}\n\ninclude!("r17_g_powers.rs");', start)
s = s[:start] + '    fast_g::apply(coin_weights, weights);' + s[end:]
s += '\n#[path="r17_fast_g.rs"] mod fast_g;\n'
path.write_text(s)
change = {'before_sha256': hashlib.sha256(before).hexdigest(),
          'after_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
for name in ['r17_fast_g.rs', 'r17_fast_g_generate.rs']:
    data = Path(__file__).with_name(name).read_bytes()
    (root / name).write_bytes(data)
    change[name] = hashlib.sha256(data).hexdigest()
gate = root / 'r17_tensor_check.rs'
gate.write_text(one_replace(gate.read_text(), '    r17_mask_workspace::check_fixed_table();',
    '    r17_mask_workspace::check_fixed_table();\n    r17_mask_workspace::check_fast_map();', 'fast map gate'))
path.write_text(path.read_text() + '\n#[cfg(not(performance_sbf))]\npub(super) fn check_fast_map() { fast_g::check(); }\n')
change['after_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
meta['workspace_sha256'] = change['after_sha256']
meta['fast_g'] = change
manifest = root / 'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text() + '\n[[bin]]\nname="r17-fast-g-generate"\npath="../r17_fast_g_generate.rs"\n')
(a.output / 'r17-sbf-probe.json').write_text(json.dumps(meta, indent=2) + '\n')
