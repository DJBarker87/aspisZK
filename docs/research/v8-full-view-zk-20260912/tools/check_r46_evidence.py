#!/usr/bin/env python3
"""Audit the exact-field normalization bridge; do not promote it to privacy."""
import argparse
import hashlib
import json
import re
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r46-source-normalization'
base='d98154910d890687de0c031635aadd7dbe9dd94d'
checks=[('a','WideFactorLeading',9),('c','SourceFactorEvaluation',9),
        ('e','DescendingRemainder',10),('g','NormalizationLoopBridge',8),
        ('h','SourceNormalizationBoundary',1)]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((e/'lean-h/metadata.json').read_text())
assert len(records)==227
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(root/'lean'/(r['target_name']+'.lean'))==r['source_sha256']
for name,digest in json.loads((root/'evidence/r45-source-mask-transport/SOURCE_PINS.json').read_text()).items():
    assert sha(repo/name)==digest,name

stage=json.loads((root/'evidence/r43-high-query-witness/rust-i/r18-stage.json').read_text())
sources={
    'r43_universal_witness.rs':root/'tools/r43_universal_witness.rs',
    'r28_source_helpers.rs':root/'evidence/r31-sparse-g-inverse/source/docs/research/v8-no-work-100-20260907/experiments/r28_source_helpers.rs',
}
for name,path in sources.items():
    assert sha(path)==stage['files']['docs/research/v8-no-work-100-20260907/experiments/'+name]
assert sources['r43_universal_witness.rs'].read_bytes()==(root/'evidence/r43-high-query-witness/rust-i/r43_universal_witness.rs').read_bytes()
results={}
for letter,name,audits in checks:
    path=e/f'lean-{letter}/{name}.log';log=path.read_text()
    assert '\tExit status: 0' in log and '\tSwaps: 0' in log
    assert 'error:' not in log and 'sorryAx' not in log
    axioms=re.findall(r'depends on axioms: \[([^]]*)\]',log)
    assert len(axioms)==audits
    for ax in axioms:
        assert set(re.sub(r'\s','',ax).split(','))<={'propext','Classical.choice','Quot.sound'}
    time=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':')
    results[name]={'exit':0,'swaps':0,'axioms_audited':audits,
        'wall_seconds':round(sum(float(t)*60**i for i,t in enumerate(reversed(time))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1))}
    source=(root/f'lean/AspisV8R19/{name}.lean').read_text()
    assert len(re.findall(r'^theorem ',source,re.M))==audits
    assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth|norm_num)\b',source)
    r=next(r for r in records if r['target_name']==f'AspisV8R19/{name}')
    assert r['base_revision']==base and f'/aspis-r46-lean-20260929-{letter}/lib/' in r['command'][6]
for letter,name in [('b','SourceFactorEvaluation'),('d','DescendingRemainder'),('f','NormalizationLoopBridge')]:
    assert '\tExit status: 1' in (e/f'lean-{letter}/{name}.log').read_text()
receipt={
    'base_revision':base,'new_theorems':37,'final_cache_objects':227,'targets':results,
    'wall_seconds':round(sum(r['wall_seconds']for r in results.values()),2),
    'peak_rss_kib':max(r['peak_rss_kib']for r in results.values()),
    'resources':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128,
                 'host_ram_gib':62,'available_before_gib':46,'max_simultaneous_reservation_gib':5},
    'all_degree_22_through_31_pivots_nonzero':True,
    'descending_remainder_is_unique_low_interpolant':True,
    'sequential_writes_and_order_exact_field_model':True,
    'normalized_source_quotient_eq_proved_section':True,
    'legal_G_boundary_composed':True,
    'Aeneas_extraction_or_Rust_word_refinement':False,
    'actual_circle_raw_evaluator_composition':False,
    'all_residual_source_equations':False,'new_fixed_query_polynomial_degree':False,
    'source_shared_oracle_law':False,'full_privacy':False,
    'production_or_verifier_changed':False,'new_Rust_execution':False,'new_SBF_measurement':False,
}
pins={str((root/'lean'/(r['target_name']+'.lean')).relative_to(repo)):r['source_sha256']for r in records}
for path in [root/'tools/run_r46_lean.py',*sources.values(),root/'evidence/r43-high-query-witness/rust-i/r18-stage.json']:
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
print(json.dumps({'status':'PASS','artifacts':len(manifest),**{k:receipt[k]for k in
    ('new_theorems','wall_seconds','peak_rss_kib','full_privacy','new_SBF_measurement')}},indent=2))
