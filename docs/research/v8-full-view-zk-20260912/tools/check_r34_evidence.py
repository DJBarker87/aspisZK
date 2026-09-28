#!/usr/bin/env python3
"""Offline release-receipt validation; not a universal privacy certificate."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r34-low-residual-factor';prior=root/'evidence/r33-admissible-g-residual'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
r=json.loads((e/'receipt.json').read_text());assert r['source_pins']==189 and r['actual_prefixes']==2
assert not any(r[k]for k in['source_prefix_substituted','full_privacy','universal_residual_coverage','verifier_changed'])
m=json.loads((e/'r18-stage.json').read_text());old=json.loads((prior/'r18-stage.json').read_text());ex='docs/research/v8-no-work-100-20260907/experiments/'
assert r['source_manifest_sha256']==sha(e/'r18-stage.json')and len(m['files'])==189
assert m['r34_factor']['control_manifest_sha256']==sha(prior/'r18-stage.json')
for n,h in old['files'].items():
    if n!=ex+'performance-host/Cargo.toml':assert m['files'][n]==h,n
for n,h in m['files'].items():
    if(e/'source'/n).exists():assert sha(e/'source'/n)==h,n
assert sha(root/'tools/r34_low_factor.rs')==m['files'][ex+'r34_low_factor.rs']
runtime=json.loads((e/'runtime/metadata.json').read_text());assert runtime['source_manifest_sha256']==sha(e/'r18-stage.json')and runtime['overflow_checks']and not runtime['source_prefix_substituted']
for label in['compile','world0','world1']:
    log=(e/f'runtime/{label}.log').read_text();assert '\tExit status: 0'in log and '\tSwaps: 0'in log
for w in range(2):
    assert sha(e/f'prefix/world{w}.bin')==m['r28_h1_capacity']['prefixes'][w]['prefix_sha256']
    assert sha(e/f'prefix/world{w}-r33-minor.bin')==sha(prior/f'runtime/world{w}/residual-minor.bin')
    s=json.loads((e/f'runtime/world{w}/summary.json').read_text())
    assert [s[k]for k in['source_low_weight_equalities','source_minor_entries','basis_vector_equalities','residual_basis_equalities','coefficient_probes','coefficient_reconstruction_equalities','determinant_scale_half_exponent','negative_controls']]==[216,169,13312,221,299,221,269,2]
    assert not s['full_privacy']and not s['universal_coverage']
records=json.loads((e/'lean-b/metadata.json').read_text());assert len(records)==18
for r in records:assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))and r['toolchain']=='leanprover/lean4:v4.32.0'
log=(e/'lean-b/LowResidualFactor.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==8 and '\tExit status: 0'in log and '\tSwaps: 0'in log
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_declarations':8,'actual_prefixes':2,'algebra_probes':598,'universal_residual_coverage':False,'full_privacy':False,'verifier_changed':False},indent=2))
