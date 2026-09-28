#!/usr/bin/env python3
"""Check source restrictions/evidence without promoting a host witness to Lean."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r37-source-restricted-residual';prior=root/'evidence/r36-source-residual-model'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
r=json.loads((e/'receipt.json').read_text());assert r['source_pins']==192 and r['actual_prefixes']==2 and r['algebraic_witnesses']==1
assert not any(r[k]for k in['source_prefix_substituted','full_privacy','universal_residual_coverage','nonzero_kernel_certificate','verifier_changed'])
m=json.loads((e/'r18-stage.json').read_text());old=json.loads((prior/'r18-stage.json').read_text());ex='docs/research/v8-no-work-100-20260907/experiments/'
assert r['source_manifest_sha256']==sha(e/'r18-stage.json')and len(m['files'])==192
assert m['r37_restricted']['control_manifest_sha256']==sha(prior/'r18-stage.json')
for n,h in old['files'].items():
    if n!=ex+'performance-host/Cargo.toml':assert m['files'][n]==h,n
for n,h in m['files'].items():
    if(e/'source'/n).exists():assert sha(e/'source'/n)==h,n
assert sha(root/'tools/r37_restricted_residual.rs')==m['files'][ex+'r37_restricted_residual.rs']
fragment=(root/'tools/r36_residual_model.rs').read_text().split('fn main(){')[0].replace('//!','//')
assert(e/('source/'+ex+'r37_residual_arithmetic.rs')).read_text()==fragment
runtime=json.loads((e/'runtime/metadata.json').read_text());assert runtime['source_manifest_sha256']==sha(e/'r18-stage.json')and runtime['overflow_checks']
for label in['compile','checks']:
    log=(e/f'runtime/{label}.log').read_text();assert '\tExit status: 0'in log and '\tSwaps: 0'in log
for w in range(2):
    assert sha(e/f'prefix/world{w}.bin')==m['r28_h1_capacity']['prefixes'][w]['prefix_sha256']
    assert sha(e/f'prefix/world{w}-r36-minor.bin')==sha(prior/f'runtime/world{w}/model-minor.bin')
    assert(e/f'runtime/results/world{w}-normalized.bin').stat().st_size==2704
s=json.loads((e/'runtime/results/summary.json').read_text());assert [s[k]for k in['actual_prefixes','root_coefficient_checks','scaled_minor_checks','determinant_scale_exponent','algebraic_witnesses','algebraic_witness_determinant_m31']]==[2,46,338,13,1,1171866436]
assert not any(s[k]for k in['algebraic_witness_source_prefix','nonzero_kernel_certificate','full_privacy'])
b=(e/'runtime/results/algebraic-witness-minor.bin').read_bytes();assert len(b)==2704
for i in range(0,len(b),16):assert b[i+4:i+16]==bytes(12)and int.from_bytes(b[i:i+4],'little')<2147483647
records=json.loads((e/'lean-b/metadata.json').read_text());assert len(records)==24
for r in records:assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))and r['toolchain']=='leanprover/lean4:v4.32.0'
for folder,name,count in[('a','ResidualHomogeneous',6),('b','SourceResidualPolynomial',5)]:
    log=(e/f'lean-{folder}/{name}.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count and '\tExit status: 0'in log and '\tSwaps: 0'in log
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_declarations':11,'actual_prefixes':2,'algebraic_witnesses':1,'nonzero_kernel_certificate':False,'full_privacy':False},indent=2))
