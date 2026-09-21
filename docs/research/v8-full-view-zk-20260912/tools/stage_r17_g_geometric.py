#!/usr/bin/env python3
"""Stage the exact base-field geometric specialization as an independent gate."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();assert not a.output.exists()
control=json.loads((a.stage/'r17-compact-control.json').read_text())
for name,sha in control['files'].items():
    assert hashlib.sha256((a.stage/EXPERIMENTS/name).read_bytes()).hexdigest()==sha
shutil.copytree(a.stage,a.output);root=a.output/EXPERIMENTS
meta=json.loads((a.output/'r17-sbf-probe.json').read_text())
meta['g_geometric_files']={}
for name in ['r17_g_geometric.rs','r17_g_geometric_check.rs']:
    (root/name).write_bytes(Path(__file__).with_name(name).read_bytes())
    sha=hashlib.sha256((root/name).read_bytes()).hexdigest()
    meta['g_geometric_files'][name]=sha;control['files'][name]=sha
manifest=root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text()+'\n[[bin]]\nname="r17-g-geometric-check"\npath="../r17_g_geometric_check.rs"\n')
control['bin']='r17-g-geometric-check'
control['scope']='same geometric functional specialized only at public M31 nodes'
(a.output/'r17-compact-control.json').write_text(json.dumps(control,indent=2)+'\n')
(a.output/'r17-sbf-probe.json').write_text(json.dumps(meta,indent=2)+'\n')
