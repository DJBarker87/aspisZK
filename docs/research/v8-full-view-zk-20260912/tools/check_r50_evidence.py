#!/usr/bin/env python3
"""Verify full-support fixed-query polynomial, degree and source-gate receipts."""
import argparse
import hashlib
import json
import re
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r50-fixed-query-polynomial'
base='559e73c6648f42241e998c4e9f3221082da1594a'
checks=[('c','FixedQueryModel',5),('d','FixedQuerySource',6),('e','FixedQueryPolynomial',4),
        ('h','FixedQueryDegree',9),('i','FixedQueryNonzero',4),
        ('j','FixedQueryChordScale',8),('j','FixedQuerySourceGate',2)]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((e/'lean-j/metadata.json').read_text());assert len(records)==257
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(root/'lean'/(r['target_name']+'.lean'))==r['source_sha256']
for name,digest in json.loads((root/'evidence/r49-source-g-boundary/SOURCE_PINS.json').read_text()).items():
    assert sha(repo/name)==digest,name
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
    assert r['base_revision']==base and f'/aspis-r50-lean-20260929-{letter}/lib/' in r['command'][6]
for letter,name in [('a','FixedQueryModel'),('b','FixedQueryModel'),('c','FixedQuerySource'),
                    ('d','FixedQueryPolynomial'),('f','FixedQueryDegree'),('g','FixedQueryDegree'),
                    ('h','FixedQueryNonzero'),('i','FixedQueryChordScale')]:
    assert '\tExit status: 1' in (e/f'lean-{letter}/{name}.log').read_text()
receipt={
    'base_revision':base,'new_theorems':38,'final_cache_objects':257,'targets':results,
    'new_leaf_wall_seconds':round(sum(v['wall_seconds']for v in results.values()),2),
    'peak_success_rss_kib':max(v['peak_rss_kib']for v in results.values()),
    'resources':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':5},
    'full_support_source_matrix_evaluation':True,'G_boundary_retained':True,
    'fixed_query_determinant_total_degree_bound':819,'active_challenge_coordinates':14,
    'query_roots_are_fixed_parameters':True,'unused_storage_coordinates_irrelevant':True,
    'nonzero_for_each_distinct_QM31_root_tuple':True,'rational_chord_scale_power':13,
    'rational_source_nonsingular_iff_polynomial_nonzero':True,
    'source_shared_oracle_joint_law':False,'numerical_source_failure_probability':None,
    'Rust_word_and_prepared_kernel_refinement':False,'full_privacy':False,'verifier_changed':False,
    'new_Rust_execution':False,'new_SBF_measurement':False,
}
pins={str((root/'lean'/(r['target_name']+'.lean')).relative_to(repo)):r['source_sha256']for r in records}
for path in [root/'tools/run_r50_lean.py',root/'tools/check_r50_evidence.py',
             root/'evidence/r49-source-g-boundary/SOURCE_PINS.json']:
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
    ('new_theorems','new_leaf_wall_seconds','peak_success_rss_kib','fixed_query_determinant_total_degree_bound',
     'full_privacy','new_SBF_measurement')}},indent=2))
