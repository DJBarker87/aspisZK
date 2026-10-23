#!/usr/bin/env python3
"""Audit focused native validator certificates; no verification replay."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s6-full-forest-native'
load=lambda p:json.loads(p.read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
for key,count in [('snapshot',151),('afterstate',125)]:
 root=E/(key+'-validator');r=load(root/'attempt/receipt.json')
 assert r['exit_status']==0 and r['swaps']==0
 assert r['limits']['memory.swap.max']=='0' and r['limits']['memory.max']=='8589934592'
 for path,h in load(root/'manifest.json')['files'].items():assert sha((root/path).read_bytes())==h
 assert all(load(root/'attempt/all-local-after.json')['unchanged'].values())
 assert f'0 of {count} failed' in (root/'attempt/stdout.log').read_text()
 assert sha((root/'runner.py').read_bytes())==load(root/'attempt/input.json')['runner_sha256']
 src=root/'input/frozen-source/crates/aspis-statement'
 binding=load(root/'input/source-binding.json')
 frozen=load(root/'input/frozen-statement-binding.json')
 for rel,h in frozen['source_files'].items():
  raw=(src/rel).read_text()
  extra=binding['proof_only_wrappers'].get(Path(rel).name,'')
  if extra:assert raw.endswith(extra);raw=raw[:-len(extra)]
  assert sha(raw.encode())==h,(key,rel)
 harness=(root/'input/src/lib.rs').read_text()
 assert '#[kani::stub' not in harness and 'kani::assume' not in harness
 assert binding['original_snapshot'] in (src/'src/pool_v1/pair_tree_profile.rs').read_text()
 assert binding['original_afterstate'] in (src/'src/pool_v1/pair_terminal.rs').read_text()
print('Native complete snapshot/afterstate validator equality checked; whole S6 remains open.')
