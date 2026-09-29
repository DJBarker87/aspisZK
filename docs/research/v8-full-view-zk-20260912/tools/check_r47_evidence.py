#!/usr/bin/env python3
"""Verify R47 evaluator/fold receipts without rerunning unchanged suites."""
import argparse
import hashlib
import json
import re
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r47-circle-opening-bridge'
base='3cd200321280562f05514a9f8dfa0b713cb25d53'
checks=[('b','AspisV8R19/CircleWeightBridge',8),('f','AspisV8R19/CircleChannelsBridge',7),
        ('g','AspisV8R19/CircleObservationBridge',8),('h','AspisV8R19/PreparedCircleFold',2),
        ('i','AspisV8R19/SourceCircleBoundary',5),('a','AspisFormal/V5FriNaturalBasisRadix4',1)]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((e/'lean-i/metadata.json').read_text());assert len(records)==233
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(root/'lean'/(r['target_name']+'.lean'))==r['source_sha256']
for name,digest in json.loads((root/'evidence/r46-source-normalization/SOURCE_PINS.json').read_text()).items():
    assert sha(repo/name)==digest,name
original=repo/'AspisFormal/AspisFormal/V5FriNaturalBasisRadix4.lean'
assert original.read_bytes()==(root/'lean/AspisFormal/V5FriNaturalBasisRadix4.lean').read_bytes()
source=root/'evidence/r42-admissible-grid/source/crates/aspis-core/src/circle_fri.rs'
stage=root/'evidence/r43-high-query-witness/rust-i/r18-stage.json'
assert sha(source)==json.loads(stage.read_text())['files']['crates/aspis-core/src/circle_fri.rs']
results={}
for letter,name,audits in checks:
    log=(e/f'lean-{letter}/{Path(name).name}.log').read_text()
    assert '\tExit status: 0' in log and '\tSwaps: 0' in log
    assert 'error:' not in log and 'sorryAx' not in log
    axioms=re.findall(r'depends on axioms: \[([^]]*)\]',log);assert len(axioms)==audits
    for ax in axioms:
        assert set(re.sub(r'\s','',ax).split(','))<={'propext','Classical.choice','Quot.sound'}
    ts=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':')
    results[name]={'exit':0,'swaps':0,'axioms_audited':audits,
        'wall_seconds':round(sum(float(t)*60**i for i,t in enumerate(reversed(ts))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1))}
    src=(root/'lean'/(name+'.lean')).read_text()
    if name.startswith('AspisV8R19/'):
        assert len(re.findall(r'^theorem ',src,re.M))==audits
        assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth|norm_num)\b',src)
    r=next(r for r in records if r['target_name']==name)
    assert r['base_revision']==base and f'/aspis-r47-lean-20260929-{letter}/lib/' in r['command'][6]
for letter,name in [('a','CircleWeightBridge'),('c','CircleChannelsBridge'),
                    ('d','CircleChannelsBridge'),('e','CircleChannelsBridge')]:
    assert '\tExit status: 1' in (e/f'lean-{letter}/{name}.log').read_text()
assert 'maximum number of heartbeats' in (e/'lean-a/CircleWeightBridge.log').read_text()
assert 'selector_certificate' not in (root/'lean/AspisV8R19/CircleWeightBridge.lean').read_text()
receipt={
    'base_revision':base,'new_theorems':30,'retained_axioms_audits':1,'final_cache_objects':233,
    'targets':results,'new_leaf_wall_seconds':round(sum(v['wall_seconds']for n,v in results.items()if n.startswith('AspisV8R19/')),2),
    'all_selected_wall_seconds':round(sum(v['wall_seconds']for v in results.values()),2),
    'peak_success_rss_kib':max(v['peak_rss_kib']for v in results.values()),
    'resources':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':5},
    'symbolic_source_bit_selector_bridge':True,'circle_four_channel_decomposition':True,
    'exact_field_raw_chord_division_fold_composed':True,'prepared_polynomial_fold_arithmetic_bound':True,
    'all_source_sampler_fibre_premises_formalized':False,'Rust_word_and_prepared_kernel_refinement':False,
    'remaining_point_and_relation_polynomial_source_equations':False,
    'new_fixed_query_degree':False,'source_shared_oracle_law':False,'full_privacy':False,
    'verifier_changed':False,'new_Rust_execution':False,'new_SBF_measurement':False,
}
pins={str((root/'lean'/(r['target_name']+'.lean')).relative_to(repo)):r['source_sha256']for r in records}
for path in [root/'tools/run_r47_lean.py',original,source,stage,
             root/'evidence/r31-sparse-g-inverse/source/docs/research/v8-no-work-100-20260907/experiments/r28_source_helpers.rs']:
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
    ('new_theorems','new_leaf_wall_seconds','all_selected_wall_seconds','peak_success_rss_kib','full_privacy','new_SBF_measurement')}},indent=2))
