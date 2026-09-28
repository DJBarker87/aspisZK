#!/usr/bin/env python3
"""Validate the formal/source receipt, without claiming global privacy."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r35-factor-leading'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
r=json.loads((e/'receipt.json').read_text());assert r['unchanged_source_pins']==189
assert r['source_manifest_sha256']==sha(root/'evidence/r34-low-residual-factor/r18-stage.json')
assert not any(r[k]for k in['full_privacy','universal_residual_coverage','verifier_changed','new_rust_or_sbf_run'])
records=json.loads((e/'lean-c/metadata.json').read_text());assert len(records)==19
for r in records:assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))and r['toolchain']=='leanprover/lean4:v4.32.0'
log=(e/'lean-c/FactorLeading.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==13 and '\tExit status: 0'in log and '\tSwaps: 0'in log
source=(root/'lean/AspisV8R19/FactorLeading.lean').read_text();assert 'sorry'not in source and 'axiom 'not in source
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_declarations':13,'unchanged_source_pins':189,'factor_determinant_universal_in_roots':True,'universal_residual_coverage':False,'full_privacy':False},indent=2))
