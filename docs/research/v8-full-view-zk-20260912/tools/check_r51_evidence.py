#!/usr/bin/env python3
"""Check the R51 focused proofs, unchanged source pins and new control receipts."""
import argparse
import hashlib
import json
import re
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r51-duplex-first-hit'
base='e5d3c322dd27c3c90b5b486a4ceea9db74564d2e'
checks=[('b','DuplexFrames',9,9),('d','DuplexFreshPair',5,7),
        ('e','SourceDuplexStep',9,10),('i','UniformStateFirstHit',4,4)]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(log):
    assert '\tExit status: 0' in log and '\tSwaps: 0' in log
    assert 'error:' not in log and 'sorryAx' not in log
    ts=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':')
    return {'exit':0,'swaps':0,
        'wall_seconds':round(sum(float(t)*60**i for i,t in enumerate(reversed(ts))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1))}
records=json.loads((e/'lean-i/metadata.json').read_text());assert len(records)==263
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(root/'lean'/(r['target_name']+'.lean'))==r['source_sha256']
for name,digest in json.loads((root/'evidence/r50-fixed-query-polynomial/SOURCE_PINS.json').read_text()).items():
    assert sha(repo/name)==digest,name
results={}
for letter,name,theorems,audits in checks:
    log=(e/f'lean-{letter}/{name}.log').read_text();result=metrics(log)
    axioms=re.findall(r'depends on axioms: \[([^]]*)\]',log);assert len(axioms)==audits
    for ax in axioms:
        assert set(re.sub(r'\s','',ax).split(','))<={'propext','Classical.choice','Quot.sound'}
    result.update(theorems=theorems,axioms_audited=audits);results[name]=result
    src=(root/'lean/AspisV8R19'/(name+'.lean')).read_text()
    assert len(re.findall(r'^theorem ',src,re.M))==theorems
    assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth|norm_num)\b',src)
    r=next(r for r in records if r['target_name']=='AspisV8R19/'+name)
    assert r['base_revision']==base and f'/aspis-r51-lean-20260929-{letter}/lib/' in r['command'][6]
for letter,name in [('a','DuplexFrames'),('c','DuplexFreshPair'),
                    ('f','UniformStateFirstHit'),('g','UniformStateFirstHit'),('h','UniformStateFirstHit')]:
    assert '\tExit status: 1' in (e/f'lean-{letter}/{name}.log').read_text()
# Recompiled only these missing unchanged dependencies; audit them as well.
for name,audits in [('FiniteGames',3),('AdaptiveOracle',6)]:
    log=(e/f'lean-d/{name}.log').read_text();metrics(log)
    ax=re.findall(r'depends on axioms: \[([^]]*)\]',log);assert len(ax)==audits
    for x in ax:assert set(re.sub(r'\s','',x).split(','))<={'propext','Classical.choice','Quot.sound'}
parent_path=root/'evidence/r42-admissible-grid/query/r18-stage.json'
parent=json.loads(parent_path.read_text());stage=json.loads((e/'source/r18-stage.json').read_text())
meta=json.loads((e/'source/metadata.json').read_text())
assert len(parent['files'])==197 and len(stage['files'])==198
assert stage['r51_query_control']['control_manifest_sha256']==sha(parent_path)
assert stage['r51_query_control']['parent_revision']==base
assert stage['r51_query_control']['verifier_changed'] is False
manifest_name='docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'
for name,digest in parent['files'].items():
    if name!=manifest_name:assert stage['files'][name]==digest,name
test_name='docs/research/v8-no-work-100-20260907/experiments/r51_query_control.rs'
assert set(stage['files'])-set(parent['files'])=={test_name}
assert stage['files'][test_name]==sha(root/'tools/r51_query_control.rs')
transcript=repo/'crates/aspis-core/src/transcript.rs'
assert stage['files']['crates/aspis-core/src/transcript.rs']==sha(transcript)
assert meta['source_manifest_sha256']==sha(e/'source/r18-stage.json')
assert meta['overflow_checks'] and not meta['sampler_law'] and not meta['full_privacy']
for command in meta['commands']:assert command['exit']==0
assert all(x in meta['commands'][0]['command']for x in ['--release','--locked','--offline'])
assert meta['commands'][0]['command'][meta['commands'][0]['command'].index('--jobs')+1]=='2'
rust={name:metrics((e/f'source/{name}.log').read_text())for name in ['compile','query-control']}
control=(e/'source/query-control.log').read_text()
for field in ['advancing_pairs=64','repeated_state_controls=1','prior_read_controls=2',
    'absorb_equivalence_cases=15','rejection_controls=2','repeated_failure_controls=1',
    'actual_source=true','memoized_script=true','source_probability=false','full_privacy=false']:
    assert field in control
receipt={'base_revision':base,'new_theorems':27,'new_axioms_audits':30,
    'final_cache_objects':263,'targets':results,'Rust':rust,
    'new_leaf_wall_seconds':round(sum(v['wall_seconds']for v in results.values()),2),
    'peak_success_rss_kib':max(v['peak_rss_kib']for v in results.values()),
    'resources':{'LeanHigh':'3G','LeanMax':'5G','RustHigh':'5G','RustMax':'7G',
        'MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':12},
    'exact_byte_frame_first_hit_classification':True,'fresh_pair_fiber_equivalence':True,
    'uniform_state_only_bound':'prior_read_count / 256^32',
    'source_shared_oracle_joint_law':False,'numerical_source_privacy_bound':None,
    'Rust_extraction':False,'full_privacy':False,'verifier_changed':False,
    'new_Rust_execution':True,'new_SBF_measurement':False}
pins={str((root/'lean'/(r['target_name']+'.lean')).relative_to(repo)):r['source_sha256']for r in records}
for path in [root/'tools/run_r50_lean.py',root/'tools/run_r51_lean.py',
             root/'tools/run_r42_root_support.py',root/'tools/run_r51_source.py',
             root/'tools/r51_query_control.rs',root/'tools/check_r51_evidence.py',
             root/'evidence/r50-fixed-query-polynomial/SOURCE_PINS.json',parent_path,transcript]:
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
    ('new_theorems','new_axioms_audits','new_leaf_wall_seconds','peak_success_rss_kib',
     'full_privacy','new_Rust_execution','new_SBF_measurement')}},indent=2))
