#!/usr/bin/env python3
"""Stage retained proofs with a pinned import-only FusedRows adapter.

The frozen baseline proof file and its historical source pin stay unchanged.
No theorem statement or proof body is edited in the adapter.
"""
import argparse
import hashlib
import json
from pathlib import Path
from reconstruct_generated_inputs import one_replace

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
assert not a.output.exists()
research=Path('docs/research/v8-full-view-zk-20260912/lean')
baseline=Path('docs/research/v8-no-work-100-20260907/experiments/FusedRows.lean')
sources={
    'AspisV8R16/BalancedTransport.lean':research/'AspisV8R16/BalancedTransport.lean',
    'AspisV8R16/TransportDual.lean':research/'AspisV8R16/TransportDual.lean',
    'AspisV8Baseline/FusedRows.lean':baseline,
    'AspisV8R17/CompactTransport.lean':research/'AspisV8R17/CompactTransport.lean',
}
pins={}
for name,source in sources.items():
    data=(a.repo/source).read_bytes()
    transformed=data
    if source==baseline:
        assert hashlib.sha256(data).hexdigest()=='a827b5f0b32e1b893d67615a96672d203bf34a9c0c027345bd698175e2999a38'
        transformed=one_replace(data.decode(),'import Mathlib.Tactic\n',
            'import Mathlib.Tactic.FinCases\nimport Mathlib.Tactic.Ring\n',
            'narrow imports; retain all theorem statements and proof bodies').encode()
    dest=a.output/name
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(transformed)
    pins[name]={'source':str(source),'source_sha256':hashlib.sha256(data).hexdigest(),
        'staged_sha256':hashlib.sha256(transformed).hexdigest()}
(a.output/'r17-compact-lean-pins.json').write_text(json.dumps({
    'source_base':'5306811d69191ef4d875700dc95c52ce1b484baa','files':pins,
},indent=2)+'\n')
