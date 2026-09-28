#!/usr/bin/env python3
"""Offline integrity/boundary gate. No repeated heavy proof or source replay."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r31-sparse-g-inverse'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
receipt=json.loads((e/'receipt.json').read_text());assert receipt['pins']==187 and not receipt['verifier_changed']and not receipt['full_privacy']
assert receipt['algebraic_witness_only']and receipt['normalized_witness_sampler_excluded']
m=json.loads((e/'r18-stage.json').read_text());assert len(m['files'])==187 and receipt['source_manifest_sha256']==sha(e/'r18-stage.json')
control=json.loads((root/'evidence/r30-query-kernel/r18-stage.json').read_text());ex='docs/research/v8-no-work-100-20260907/experiments/'
assert m['r31_inverse']['control_manifest_sha256']==sha(root/'evidence/r30-query-kernel/r18-stage.json')
for n,h in control['files'].items():
    if n != ex+'performance-host/Cargo.toml':assert m['files'][n]==h,n
for n,h in m['files'].items():
    p=e/'source'/n
    if p.exists():assert sha(p)==h,n
assert sha(root/'tools/r31_sparse_g_inverse.rs')==m['files'][ex+'r31_sparse_g_inverse.rs']
s=json.loads((e/'runtime/result/summary.json').read_text())
assert [s[x]for x in['selected_columns','pair_blocks','singletons','source_matrix_entries_checked','inverse_coordinates_checked','negative_controls']]==[271,68,135,146882,73441,136]
cols=[3*((128+3*i)//4-22)+(1 if (128+3*i)%4==0 else (128+3*i)%4)-1 for i in range(271)]
assert s['columns']==cols and len(set(cols))==271 and max(cols)<699
assert s['normalized_chord']==[2,0,0]and s['normalized_witness_sampler_excluded']
assert not any(s[k]for k in['actual_transcript_generated','all_source_prefixes_covered','full_privacy'])
for name in ['compile','source-check']:
    log=(e/f'runtime/{name}.log').read_text();assert '\tExit status: 0'in log and '\tSwaps: 0'in log
records=json.loads((e/'lean/metadata.json').read_text());assert len(records)==2
for rec,leaf,count in zip(records,['SparseGCoreInverse','SparseGChordWitness'],[12,5]):
    assert rec['exit']==0 and rec['source_sha256']==sha(root/'lean/AspisV8R19'/(leaf+'.lean'))
    log=(e/'lean'/(leaf+'.log')).read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count and '\tSwaps: 0'in log and '\tExit status: 0'in log
old=json.loads((root/'evidence/r30-query-kernel/lean/metadata.json').read_text())[0]
assert json.loads((e/'lean/reused-object.json').read_text())['source_sha256']==old['source_sha256']==sha(root/'lean/AspisV8R17/SourceScatter.lean')
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_leaves':17,'source_entries_checked':146882,'algebraic_witness_only':True,'normalized_witness_sampler_excluded':True,'all_source_prefixes_covered':False,'full_privacy':False,'verifier_changed':False},indent=2))
