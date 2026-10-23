#!/usr/bin/env python3
"""Check retained experiments; do not replay failed whole-point checks."""
from pathlib import Path
import hashlib, json
R=Path(__file__).resolve().parents[2]
P=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-claim-uf'
load=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(P/'manifest.json')
assert set(m['files'])=={str(p.relative_to(P)) for p in P.rglob('*') if p.is_file()}-{'manifest.json'}
for rel,d in m['files'].items():assert sha(P/rel)==d,rel
assert not any(p.suffix in ['.o','.out','.olean','.rlib','.exe','.pyc','.llbc'] for p in P.rglob('*'))
positive=['s1-uf-positive-v1','s1-uf-rust-positive-v2','s1-uf-push-positive-v1','s1-uf-push-ssa-positive-v1']
negative=['s1-uf-negative-v1','s1-uf-rust-negative-v1','s1-uf-push-negative-v1','s1-uf-push-ssa-negative-v1']
failed=['s1-original-point-fission-v1','s1-original-point-uf-v1','s1-original-point-pure-push-v1','s1-original-point-pure-push-ssa-v1','s1-uf-rust-positive-v1','s1-claim-owned-nested-aeneas-v1']
positive += [f's1-claim-owned-nested-charon-v{v}' for v in range(1,8)] + ['s1-claim-owned-nested-aeneas-v7']
failed += [f's1-claim-owned-nested-aeneas-v{v}' for v in range(2,7)] + ['s1-original-point-replay-v1','s1-original-point-replay-v2','s1-original-point-replay-accepted-v1']
for tag in positive+negative+failed:
 a=P/'attempts'/tag;r=load(a/'receipt.json')
 assert r['swaps']==0 and r['limits']['memory.swap.max']=='0'
 assert (r['exit_status']==0)==(tag in positive),tag
 if tag in negative:
  assert 'assertion' in (a/'stdout.log').read_text().lower(),tag
 if (a/'all-local-after.json').is_file():
  assert all(load(a/'all-local-after.json')['unchanged'].values())
for version in ['v1','v2','v4']:
 root=P/'inputs'/('aspis-s1-claim-uf-'+version)
 binding=load(root/'uf-binding.json')
 for field,rel in [('source_sha256','src/lib.rs'),('proof_sha256','src/proofs.rs'),('c_sha256','leaves.c')]:
  assert binding[field]==sha(root/rel),(version,field)
for tag in ['s1-uf-push-positive-v1','s1-uf-push-ssa-positive-v1']:
 log=(P/'attempts'/tag/'stdout.log').read_text()
 assert '2 of 2 cover properties satisfied' in log
print(json.dumps(dict(source_only=True,tool_preflights_pass=True,negative_controls_fail_as_expected=True,
 original_point_equivalence_proved=False,owned_nested_extraction_succeeded=True,
 whole_s1_closed=False,whole_s6_closed=False)))
