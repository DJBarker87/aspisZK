#!/usr/bin/env python3
"""Stage the compact ordinary-channel evaluator and its source comparison."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--implementation',type=Path,
    default=Path(__file__).with_name('r17_compact_ordinary.rs'))
a=p.parse_args()
assert not a.output.exists()
meta=json.loads((a.stage/'r17-compact-control.json').read_text())
for name,expected in meta['files'].items():
    assert hashlib.sha256((a.stage/EXPERIMENTS/name).read_bytes()).hexdigest()==expected
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
for name in ['r17_compact_ordinary.rs','r17_compact_ordinary_check.rs']:
    source=a.implementation if name=='r17_compact_ordinary.rs' else Path(__file__).with_name(name)
    (root/name).write_bytes(source.read_bytes())
    meta['files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
for name in ['r17_opening_weights.rs','r17_structured_g.rs','r17_mask_workspace.rs',
    'r17_fast_g.rs','r17_fast_g_tables.rs','r17_hybrid_merge.rs','r17_merge_spectra.rs']:
    meta['files'][name]=hashlib.sha256((root/name).read_bytes()).hexdigest()
manifest=root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text()+'\n[[bin]]\nname="r17-compact-ordinary-check"\npath="../r17_compact_ordinary_check.rs"\n')
meta['scope']='complete ordinary-channel compact functional control, before image residuals and fresh queries; host only'
meta['bin']='r17-compact-ordinary-check'
(a.output/'r17-compact-control.json').write_text(json.dumps(meta,indent=2)+'\n')
