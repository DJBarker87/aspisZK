#!/usr/bin/env python3
"""Check compiled sampler laws and exact Lean/actual-Rust trace replay."""
import argparse
import gzip
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r53-bounded-sampler-programs'
base='a26a468746e9551769ce1d17104050e1fc1bf1fc'
checks=[('a','SamplerWords',7),('b','QM31SamplerProgram',6),
        ('d','Q22WordScan',7),('f','Q22SamplerProgram',5),
        ('g','QM31SamplerInvariants',3),('g','SamplerOracleLaws',3),
        ('i','Q22SamplerInvariants',6),('j','SamplerReplay',0)]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(log):
    assert '\tExit status: 0' in log and '\tSwaps: 0' in log
    assert 'error:' not in log and 'sorryAx' not in log
    ts=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':')
    return {'exit':0,'swaps':0,
        'wall_seconds':round(sum(float(t)*60**i for i,t in enumerate(reversed(ts))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1))}
records=json.loads((e/'lean-j/metadata.json').read_text());assert len(records)==279
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(root/'lean'/(r['target_name']+'.lean'))==r['source_sha256']
prior=root/'evidence/r52-memoized-oracle-law'
for name,digest in json.loads((prior/'SOURCE_PINS.json').read_text()).items():
    assert sha(repo/name)==digest,name
for name,digest in json.loads((prior/'MANIFEST.json').read_text()).items():
    assert sha(prior/name)==digest,name
results={}
for letter,name,count in checks:
    log=(e/f'lean-{letter}/{name}.log').read_text();result=metrics(log)
    axioms=re.findall(r'depends on axioms: \[([^]]*)\]',log)
    assert len(axioms)+log.count('does not depend on any axioms')==count
    for ax in axioms:
        assert set(re.sub(r'\s','',ax).split(','))<={'propext','Classical.choice','Quot.sound'}
    result.update(theorems=count,axioms_audited=count);results[name]=result
    src=(root/'lean/AspisV8R19'/(name+'.lean')).read_text()
    assert len(re.findall(r'^theorem ',src,re.M))==count
    assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth|norm_num)\b',src)
    r=next(r for r in records if r['target_name']=='AspisV8R19/'+name)
    assert r['base_revision']==base and f'/aspis-r53-lean-20260929-{letter}/lib/' in r['command'][6]
for letter,name in [('c','Q22WordScan'),('e','Q22SamplerProgram'),
                    ('h','Q22SamplerInvariants'),('i','SamplerReplay')]:
    assert '\tExit status: 1' in (e/f'lean-{letter}/{name}.log').read_text()
export=json.loads((e/'replay/metadata.json').read_text())
assert export['base_revision']==base and export['exit']==0
assert export['source_sha256']==sha(root/'lean/AspisV8R19/SamplerReplay.lean')
assert export['compiled_cache_metadata_sha256']==sha(e/'lean-j/metadata.json')
fixtures=gzip.decompress((e/'replay/fixtures.txt.gz').read_bytes())
assert hashlib.sha256(fixtures).hexdigest()==export['fixture_sha256']
assert len(fixtures)==export['fixture_bytes']==7754480
rows=fixtures.decode().splitlines();assert len(rows)==export['fixture_rows']==4753
kinds=Counter();calls=0
for row in rows:
    cols=row.split('|');assert len(cols)==6
    kind,freeze,raw,result,state,trace=cols
    kinds[kind]+=1;assert freeze in ('0','1')
    assert len(raw.split(','))==72 and all(0<=int(x)<2**32 for x in raw.split(','))
    assert len(state.split(','))==32 and all(0<=int(x)<256 for x in state.split(','))
    trace_bytes=[int(x)for x in trace.split(',')] if trace else []
    assert len(trace_bytes)%65==0 and all(0<=x<256 for x in trace_bytes)
    calls+=len(trace_bytes)//65
assert kinds=={'f':4684,'q':65,'ff':4} and calls==26472
parent_path=root/'evidence/r42-admissible-grid/query/r18-stage.json'
parent=json.loads(parent_path.read_text());stage=json.loads((e/'source/r18-stage.json').read_text())
meta=json.loads((e/'source/metadata.json').read_text())
assert len(parent['files'])==197 and len(stage['files'])==198
assert stage['r53_query_control']['control_manifest_sha256']==sha(parent_path)
assert stage['r53_query_control']['parent_revision']==base
assert stage['r53_query_control']['verifier_changed'] is False
manifest_name='docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'
for name,digest in parent['files'].items():
    if name!=manifest_name:assert stage['files'][name]==digest,name
test_name='docs/research/v8-no-work-100-20260907/experiments/r53_query_control.rs'
assert set(stage['files'])-set(parent['files'])=={test_name}
assert stage['files'][test_name]==sha(root/'tools/r53_query_control.rs')
transcript=repo/'crates/aspis-core/src/transcript.rs'
assert stage['files']['crates/aspis-core/src/transcript.rs']==sha(transcript)
assert meta['source_manifest_sha256']==sha(e/'source/r18-stage.json')
assert meta['fixture_sha256']==export['fixture_sha256']
assert meta['overflow_checks'] and not meta['sampler_law'] and not meta['full_privacy']
for command in meta['commands']:assert command['exit']==0
assert all(x in meta['commands'][0]['command']for x in ['--release','--locked','--offline'])
assert meta['commands'][0]['command'][meta['commands'][0]['command'].index('--jobs')+1]=='2'
rust={name:metrics((e/f'source/{name}.log').read_text())for name in ['compile','query-control']}
control=(e/'source/query-control.log').read_text()
for field in ['cases=4753','field_cases=4684','query_cases=65','sequential_cases=4',
    'hash_calls=26472','cache_hits=20','complete_trace_bytes_equal=true',
    'final_states_equal=true','results_errors_equal=true','scripted_oracle=true',
    'universal_Rust_refinement=false','source_probability=false','full_privacy=false']:
    assert field in control
receipt={'base_revision':base,'new_theorems':37,'new_axioms_audits':37,
    'final_cache_objects':279,'targets':results,'Rust':rust,
    'fixture_export':metrics((e/'replay/export.log').read_text()),
    'fixture_rows':4753,'hash_calls':26472,'cache_hits':20,
    'new_leaf_wall_seconds':round(sum(v['wall_seconds']for v in results.values()),2),
    'peak_success_rss_kib':max(v['peak_rss_kib']for v in results.values()),
    'resources':{'LeanHigh':'3G','LeanMax':'5G','RustHigh':'5G','RustMax':'7G',
        'MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':7},
    'source_shaped_QM31_and_fixed_q22_oracle_programs':True,
    'model_exact_memoized_oracle_law':True,'q22_no_artificial_cutoff':True,
    'complete_query_trace_retained':True,'compiled_wrapper_samplers':False,
    'universal_Rust_refinement':False,'whole_source_prover_refinement':False,
    'source_challenge_joint_law':False,'numerical_source_privacy_bound':None,
    'full_privacy':False,'verifier_changed':False,
    'new_Rust_execution':True,'new_SBF_measurement':False}
pins={str((root/'lean'/(r['target_name']+'.lean')).relative_to(repo)):r['source_sha256']for r in records}
for path in [root/'tools'/n for n in ['run_r50_lean.py','run_r53_lean.py','run_r42_root_support.py',
    'run_r53_source.py','run_r53_replay.py','r53_query_control.rs','check_r53_evidence.py']]+[
    prior/'SOURCE_PINS.json',prior/'MANIFEST.json',parent_path,transcript]:
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
     'fixture_rows','hash_calls','full_privacy','new_Rust_execution','new_SBF_measurement')}},indent=2))
