#!/usr/bin/env python3
"""Check the exact formal/source boundary without replaying unchanged jobs."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r32-sparse-g-polynomial'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
receipt=json.loads((e/'receipt.json').read_text())
assert receipt['source_pins']==187 and receipt['determinant_total_degree_bound']==1355 and receipt['nonzero_polynomial_proved']
assert not any(receipt[k]for k in ['source_oracle_probability_bound_proved','full_privacy','verifier_changed'])
assert sha(e/'source-manifest.json')==receipt['source_manifest_sha256']==sha(root/'evidence/r31-sparse-g-inverse/r18-stage.json')
records=json.loads((e/'lean-d/metadata.json').read_text());assert len(records)==9
for r in records:
    assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))
    assert r['toolchain']=='leanprover/lean4:v4.32.0'
    name=Path(r['target_name']).name
    path=e/('lean-d'if name=='SparseGPolynomial'else'lean-b')/(name+'.log')
    log=path.read_text();assert 'sorryAx'not in log and '\tExit status: 0'in log and '\tSwaps: 0'in log
    if name=='SparseGPolynomial':assert log.count('depends on axioms:')==13
for letter in 'bcd':
    m=json.loads((e/f'lean-{letter}/workspace/lake-manifest.json').read_text());assert m['packages']==[]
recovery=json.loads((e/'cache-recovery.json').read_text());assert all(r['exit']==0 for r in recovery['checks'])and not recovery['dependency_cache_rebuilt']
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_declarations':13,'nonzero_source_model_polynomial':True,'total_degree_bound':1355,'outside_zero_set_core_surjectivity':True,'source_oracle_probability_bound':False,'full_privacy':False,'verifier_changed':False},indent=2))
