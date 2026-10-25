#!/usr/bin/env python3
"""Audit checked generator, raw representation extension and failed parent."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';P=E/'s1-contractgen-diagnostics-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((P/'manifest.json').read_text())
for rel,h in m['files'].items():
 p=R/rel;assert sha(p)==h,rel
 assert p.suffix not in ['.olean','.ilean','.llbc','.goto','.out','.o','.a','.rlib','.rmeta','.so','.pyc']
T=R/'tools/s1-canonical-input-contract-20261025';b=json.loads((T/'source-binding.json').read_text());original=subprocess.check_output(['git','show',b['freeze']+':crates/aspis-core/src/field/wide_exact.rs'],cwd=R)
assert hashlib.sha256(original).hexdigest()==b['original_wide_exact_sha256']
new=P/'candidate-core-source/crates/aspis-core/src/field/wide_exact.rs';assert new.read_bytes()==original+b['appended_cfg_kani_only'].encode();assert sha(new)==b['candidate_wide_exact_sha256']
for row in json.loads((P/'metrics.json').read_text())['targets']:
 A=E/row['attempt'];r=json.loads((A/'receipt.json').read_text());i=json.loads((A/'input.json').read_text());assert all(r['source_unchanged'].values())and all(r['tools_unchanged'].values())
 for file,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(A/file)==r[key]
 if row['attempt']=='s1-canonical-input-contract-v3':
  assert r['exit_status']==1 and "doesn't implement `kani::Arbitrary`"in(A/'stdout.log').read_text()
 elif row['attempt']=='s1-native-prepared-contractgen-v4':
  assert r['exit_status']==-15 and r['watchdog_stop']=='aggregate RSS watchdog'and r['swaps']is None
 else:assert r['exit_status']==0 and r['swaps']==0 and r['watchdog_stop']is None
for attempt in ['s1-canonical-input-contract-v2','s1-canonical-input-contract-v6','s1-native-prepared-contractgen-v2']:
 A=E/attempt;assert 'VERIFICATION:- SUCCESSFUL'in(A/'stdout.log').read_text()
assert json.loads((E/'s1-canonical-input-contract-v4/preflight.json').read_text())['verification_launched']is False
source=(R/'tools/s1-native-prepared-contractgen-20261025/proofs.rs').read_text();assert '#[kani::proof_for_contract(any_e)]'in source and source.count('#[kani::stub_verified(any_e)]')==7
assert 'kani::assume'not in source and 'transmute'not in source
assert source.count('#[kani::stub(')==63
print(json.dumps(dict(status='PASS',pins=len(m['files']),generator_checked=True,private_native_contract_stub_smoke_checked=True,parent_constructor_claim_closed=False,qualification='Historical25866 native core plus verification-only raw Arbitrary extension. Canonical postcondition checked before use. Not a later-release/SDK/arithmetic/security closure.')))
