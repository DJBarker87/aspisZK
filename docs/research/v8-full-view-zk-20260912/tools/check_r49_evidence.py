#!/usr/bin/env python3
"""Check R49 source-G, point-constructor and fixed residual receipts."""
import argparse
import hashlib
import json
import re
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r49-source-g-boundary'
base='510b95490b59fdb8b6887187e88400299f3687ed'
checks=[('b','SparseGScatter',7),('d','SourceGConstant',4),('e','OriginalChannelWeights',3),
        ('e','SourceStatementPoints',4),('g','SourceFixedResidual',6),
        ('h','FullWeightHom',4),('j','SourceFieldResidual',8)]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((e/'lean-j/metadata.json').read_text());assert len(records)==250
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(root/'lean'/(r['target_name']+'.lean'))==r['source_sha256']
for name,digest in json.loads((root/'evidence/r48-full-point-functional/SOURCE_PINS.json').read_text()).items():
    assert sha(repo/name)==digest,name
stage=root/'evidence/r43-high-query-witness/rust-i/r18-stage.json'
source_manifest=json.loads(stage.read_text())['files']
sources=[]
for name in ['r18_sparse_coded_g.rs','r17_structured_g.rs','r17_opening_weights.rs']:
    path=root/'evidence/r43-high-query-witness/source'/name
    assert sha(path)==source_manifest['docs/research/v8-no-work-100-20260907/experiments/'+name]
    sources.append(path)
path=repo/'crates/aspis-core/src/v6_transcript.rs'
assert sha(path)==source_manifest['crates/aspis-core/src/v6_transcript.rs'];sources.append(path)
results={}
for letter,name,audits in checks:
    log=(e/f'lean-{letter}/{name}.log').read_text()
    assert '\tExit status: 0' in log and '\tSwaps: 0' in log
    assert 'error:' not in log and 'sorryAx' not in log
    axioms=re.findall(r'depends on axioms: \[([^]]*)\]',log);assert len(axioms)==audits
    for ax in axioms:
        assert set(re.sub(r'\s','',ax).split(','))<={'propext','Classical.choice','Quot.sound'}
    ts=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':')
    results[name]={'exit':0,'swaps':0,'axioms_audited':audits,
        'wall_seconds':round(sum(float(t)*60**i for i,t in enumerate(reversed(ts))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1))}
    src=(root/'lean/AspisV8R19'/(name+'.lean')).read_text()
    assert len(re.findall(r'^theorem ',src,re.M))==audits
    assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth|norm_num)\b',src)
    r=next(r for r in records if r['target_name']=='AspisV8R19/'+name)
    assert r['base_revision']==base and f'/aspis-r49-lean-20260929-{letter}/lib/' in r['command'][6]
for letter,name in [('a','SparseGScatter'),('c','SourceGConstant'),('d','OriginalChannelWeights'),
                    ('f','SourceFixedResidual'),('i','SourceFieldResidual')]:
    assert '\tExit status: 1' in (e/f'lean-{letter}/{name}.log').read_text()
receipt={
    'base_revision':base,'new_theorems':36,'final_cache_objects':250,'targets':results,
    'new_leaf_wall_seconds':round(sum(v['wall_seconds']for v in results.values()),2),
    'peak_success_rss_kib':max(v['peak_rss_kib']for v in results.values()),
    'resources':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':5},
    'ordered_scatter_and_ten_scale_steps':True,'source_statement_point_field_loops':True,
    'ordinary_G_full_support_functional_specialization':True,'G_boundary_128_retained':True,
    'source_shaped_fixed_matrix_equal_for_all_distinct_QM31_root_tuples':True,
    'other_270_G_coin_coefficients_arbitrary':True,'fixed_specialization_accepted_prefix_claimed':False,
    'new_fixed_query_degree':False,'Rust_word_and_prepared_kernel_refinement':False,
    'source_shared_oracle_law':False,'full_privacy':False,'verifier_changed':False,
    'new_Rust_execution':False,'new_SBF_measurement':False,
}
pins={str((root/'lean'/(r['target_name']+'.lean')).relative_to(repo)):r['source_sha256']for r in records}
for path in [root/'tools/run_r49_lean.py',root/'tools/check_r49_evidence.py',
             root/'evidence/r48-full-point-functional/SOURCE_PINS.json',stage,*sources]:
    pins[str(path.relative_to(repo))]=sha(path)
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt
assert json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text())
assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for name,digest in manifest.items():assert sha(e/name)==digest,name
print(json.dumps({'status':'PASS','artifacts':len(manifest),'pins':len(pins),**{k:receipt[k]for k in
    ('new_theorems','new_leaf_wall_seconds','peak_success_rss_kib','full_privacy','new_SBF_measurement')}},indent=2))
