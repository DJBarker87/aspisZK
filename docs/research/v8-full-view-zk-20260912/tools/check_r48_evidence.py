#!/usr/bin/env python3
"""Check R48 full-support source-functional receipts, without rerunning suites."""
import argparse
import hashlib
import json
import re
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r48-full-point-functional'
base='7e78e04991e6e82411852e0f201323fc96cbf8cb'
checks=[('b','AspisV8R19/FullPointFunctional',6),('c','AspisV8R19/FullQuotientWeights',3),
        ('d','AspisV8R19/FullCoefficientBoundary',3),('f','AspisV8R19/FullResidualBoundary',5),
        ('h','AspisV8R19/FullWitnessPointCode',4),('a','AspisV8R16/TransportDual',2),
        ('a','AspisV8R17/SourceChordTranspose',3),('a','AspisV8R17/SourceOpeningResidual',4),
        ('a','AspisV8R17/TransportedOpening',2),('a','AspisV8R17/SourceOriginalWeights',5)]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((e/'lean-h/metadata.json').read_text());assert len(records)==243
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(root/'lean'/(r['target_name']+'.lean'))==r['source_sha256']
for name,digest in json.loads((root/'evidence/r47-circle-opening-bridge/SOURCE_PINS.json').read_text()).items():
    assert sha(repo/name)==digest,name
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
    assert r['base_revision']==base and f'/aspis-r48-lean-20260929-{letter}/lib/' in r['command'][6]
for letter,name in [('a','FullPointFunctional'),('e','FullResidualBoundary'),('g','FullWitnessPointCode')]:
    assert '\tExit status: 1' in (e/f'lean-{letter}/{name}.log').read_text()
receipt={
    'base_revision':base,'new_theorems':21,'retained_axioms_audits':16,'final_cache_objects':243,
    'targets':results,'new_leaf_wall_seconds':round(sum(v['wall_seconds']for n,v in results.items()if n.startswith('AspisV8R19/')),2),
    'all_selected_wall_seconds':round(sum(v['wall_seconds']for v in results.values()),2),
    'peak_success_rss_kib':max(v['peak_rss_kib']for v in results.values()),
    'resources':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':5},
    'full_131_coordinate_transport_pairing':True,'full_128_quotient_weight_entries':True,
    'all_seven_field_kernel_coefficients_restricted_exactly':True,
    'normalized_point_and_coefficient_functionals_composed':True,
    'fixed_point_witness_extra_20_coordinates_zero':True,
    'fixed_G_weight_source_specialization':False,'new_fixed_query_degree':False,
    'Rust_word_and_prepared_kernel_refinement':False,'source_shared_oracle_law':False,
    'full_privacy':False,'verifier_changed':False,'new_Rust_execution':False,'new_SBF_measurement':False,
}
pins={str((root/'lean'/(r['target_name']+'.lean')).relative_to(repo)):r['source_sha256']for r in records}
for path in [root/'tools/run_r48_lean.py',root/'tools/check_r48_evidence.py',
             root/'evidence/r47-circle-opening-bridge/SOURCE_PINS.json',
             root/'evidence/r43-high-query-witness/rust-i/r18-stage.json']:
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
