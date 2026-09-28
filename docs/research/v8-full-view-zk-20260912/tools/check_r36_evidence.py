#!/usr/bin/env python3
"""Offline source/model evidence gate, not a full Rust refinement or privacy proof."""
import hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r36-source-residual-model';prior=root/'evidence/r34-low-residual-factor'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
r=json.loads((e/'receipt.json').read_text());assert r['source_pins']==190 and r['actual_prefixes']==2
assert not any(r[k]for k in['source_prefix_substituted','full_privacy','universal_residual_coverage','verifier_changed'])
m=json.loads((e/'r18-stage.json').read_text());old=json.loads((prior/'r18-stage.json').read_text());ex='docs/research/v8-no-work-100-20260907/experiments/'
assert r['source_manifest_sha256']==sha(e/'r18-stage.json')and len(m['files'])==190
assert m['r36_model']['control_manifest_sha256']==sha(prior/'r18-stage.json')
for n,h in old['files'].items():
    if n!=ex+'performance-host/Cargo.toml':assert m['files'][n]==h,n
for n,h in m['files'].items():
    if(e/'source'/n).exists():assert sha(e/'source'/n)==h,n
assert sha(root/'tools/r36_residual_model.rs')==m['files'][ex+'r36_residual_model.rs']
runtime=json.loads((e/'runtime/metadata.json').read_text());assert runtime['source_manifest_sha256']==sha(e/'r18-stage.json')and runtime['overflow_checks']and not runtime['source_prefix_substituted']
for label in['compile','world0','world1']:
    log=(e/f'runtime/{label}.log').read_text();assert '\tExit status: 0'in log and '\tSwaps: 0'in log
for w in range(2):
    assert sha(e/f'prefix/world{w}.bin')==m['r28_h1_capacity']['prefixes'][w]['prefix_sha256']
    assert sha(e/f'runtime/world{w}/ResidualPins.lean')==sha(root/'lean/AspisV8R19/ResidualPins.lean')
    assert(e/f'runtime/world{w}/model-minor.bin').stat().st_size==2704
    s=json.loads((e/f'runtime/world{w}/summary.json').read_text())
    assert [s[k]for k in['table_checks','xentry_checks','chord_entry_checks','chord_tail_checks','point_checks','tensor_checks','transported_point_checks','low_weight_checks','quotient_checks','residual_checks','pivot_negative_entries','slot_negative_columns','negative_families']]==[2048,756,11988,108,30,3072,324,216,1404,208,324,13,4]
    assert not s['full_privacy']and not s['source_prefix_substituted']
# Independently parse generated low tables back against the pinned full source.
tables=(e/('source/'+ex+'r17_basis_tables.rs')).read_text();pins=(root/'lean/AspisV8R19/ResidualPins.lean').read_text()
order=[int(x)for x in re.search(r'ORDER:.*?= \[(.*?)\];',tables).group(1).split(',')]
inactive=[x.strip()=='true'for x in re.search(r'INACTIVE:.*?= \[(.*?)\];',tables).group(1).split(',')]
loworder=[int(x)for x in re.search(r'def order.*?=> \[(.*?)\]',pins).group(1).split(',')]
lowinactive=[x=='true'for x in re.search(r'def inactive.*?=> \[(.*?)\]',pins).group(1).split(',')]
assert loworder==order[:111]and lowinactive==[inactive[j]for j in order[:111]]
records=json.loads((e/'lean-d/metadata.json').read_text());assert len(records)==22
for r in records:assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))and r['toolchain']=='leanprover/lean4:v4.32.0'
for folder,name,count in[('c','ResidualModel',12),('d','ResidualPins',1),('d','ResidualPolynomial',3)]:
    log=(e/f'lean-{folder}/{name}.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count and '\tExit status: 0'in log and '\tSwaps: 0'in log
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_declarations':16,'actual_prefixes':2,'source_residual_entries':416,'full_privacy':False,'universal_residual_coverage':False,'verifier_changed':False},indent=2))
