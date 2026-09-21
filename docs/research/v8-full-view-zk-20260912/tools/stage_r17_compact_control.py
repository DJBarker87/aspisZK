#!/usr/bin/env python3
"""Stage a host-only baseline compact-evaluator reuse gate; no verifier edits."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
from reconstruct_generated_inputs import EXPERIMENTS

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--repo',type=Path,required=True)
a=p.parse_args()
assert not a.output.exists()
source=a.repo/EXPERIMENTS/'structured_weights.rs'
data=source.read_bytes()
s=data.decode()
start=s.index('fn block_terminal(')
end=s.index('\nfn basis(',start)
body=s[start:end]+'\n'
staged=(a.stage/EXPERIMENTS/source.name).read_text()
assert staged[staged.index('fn block_terminal('):staged.index('\nfn basis(')]+'\n'==body
shutil.copytree(a.stage,a.output)
root=a.output/EXPERIMENTS
(root/'r17_reused_block_terminal.rs').write_text(body)
name='r17_compact_transport_check.rs'
(root/name).write_bytes(Path(__file__).with_name(name).read_bytes())
manifest=root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text()+'\n[[bin]]\nname="r17-compact-transport-check"\npath="../r17_compact_transport_check.rs"\n')
names=['structured_weights.rs','r17_reused_block_terminal.rs',name,
    'r16_basis_transport.rs','r17_tensor_prefix.rs','r17_owned_weights.rs',
    'r17_host_relation.rs','relation_callback.rs']
pins={name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
for name in ['r17_host_relation.rs','relation_callback.rs']:
    assert (root/name).read_bytes()==(a.stage/EXPERIMENTS/name).read_bytes()
(a.output/'r17-compact-control.json').write_text(json.dumps({
    'scope':'host-only exact baseline function extraction and transport correction controls',
    'source_base':'5306811d69191ef4d875700dc95c52ce1b484baa',
    'baseline_structured_weights_sha256':hashlib.sha256(data).hexdigest(),
    'files':pins,
},indent=2)+'\n')
