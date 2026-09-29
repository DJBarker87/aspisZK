#!/usr/bin/env python3
"""Verify R54 wrapper proofs, exact-source replay and retained source pins."""
import argparse,gzip,hashlib,json,re
from collections import Counter
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r54-sampler-wrappers';prior=root/'evidence/r53-bounded-sampler-programs'
base='eaa0435c1e71b9605af40daf7b07cefd3bcb5e92'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(log,audits=None):
    assert '\tExit status: 0' in log and '\tSwaps: 0' in log
    assert 'error:' not in log and 'sorryAx' not in log
    ax=re.findall(r'depends on axioms: \[([^]]*)\]',log)
    if audits is not None:assert len(ax)+log.count('does not depend on any axioms')==audits
    for x in ax:assert set(re.sub(r'\s','',x).split(','))<={'propext','Classical.choice','Quot.sound'}
    ts=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':')
    return {'exit':0,'swaps':0,'axioms_audited':audits,
        'wall_seconds':round(sum(float(t)*60**i for i,t in enumerate(reversed(ts))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1))}
for name,digest in json.loads((prior/'SOURCE_PINS.json').read_text()).items():assert sha(repo/name)==digest,name
for name,digest in json.loads((prior/'MANIFEST.json').read_text()).items():assert sha(prior/name)==digest,name
records=json.loads((e/'lean-i/metadata.json').read_text());assert len(records)==286
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(root/'lean'/(r['target_name']+'.lean'))==r['source_sha256']
checks=[('a','BoundedSamplerWrapper',7),('c','SamplerWrapperPolicies',8),
        ('g','SamplerFieldDecode',7),('h','SamplerCirclePolicy',13),('i','WrapperReplay',0)]
results={}
for letter,name,count in checks:
    result=metrics((e/f'lean-{letter}/{name}.log').read_text(),count)
    result['theorems']=count;results[name]=result
    src=(root/'lean/AspisV8R19'/(name+'.lean')).read_text()
    assert len(re.findall(r'^theorem ',src,re.M))==count
    assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth|norm_num)\b',src)
    r=next(r for r in records if r['target_name']=='AspisV8R19/'+name)
    assert r['base_revision']==base and f'/aspis-r54-lean-20260929-{letter}/lib/' in r['command'][6]
for letter,name in [('b','SamplerWrapperPolicies'),('c','SamplerFieldDecode'),
    ('d','SamplerCirclePolicy'),('e','SamplerCirclePolicy'),('f','SamplerCirclePolicy'),
    ('g','SamplerCirclePolicy'),('h','WrapperReplay')]:
    assert '\tExit status: 1' in (e/f'lean-{letter}/{name}.log').read_text()
for name,count in [('CircleChord',6),('ExactTowerChord',4)]:metrics((e/f'lean-d/{name}.log').read_text(),count)
export=json.loads((e/'replay/metadata.json').read_text())
assert export['base_revision']==base and export['exit']==0
assert export['source_sha256']==sha(root/'lean/AspisV8R19/WrapperReplay.lean')
assert export['compiled_cache_metadata_sha256']==sha(e/'lean-i/metadata.json')
fixtures=gzip.decompress((e/'replay/fixtures.txt.gz').read_bytes())
assert hashlib.sha256(fixtures).hexdigest()==export['fixture_sha256']
assert len(fixtures)==export['fixture_bytes']
rows=fixtures.decode().splitlines();assert len(rows)==export['fixture_rows']==358
kinds=Counter();calls=0
for row in rows:
    cols=row.split('|');assert len(cols)==6
    kind,freeze,raw,result,state,trace=cols;kinds[kind]+=1
    assert freeze in ('0','1')
    assert len(raw.split(','))==128 and all(0<=int(x)<2**32 for x in raw.split(','))
    assert len(state.split(','))==32 and all(0<=int(x)<256 for x in state.split(','))
    values=[int(x)for x in trace.split(',')] if trace else []
    assert len(values)%65==0 and all(0<=x<256 for x in values);calls+=len(values)//65
assert kinds=={'n':179,'o':179}
parent_path=root/'evidence/r42-admissible-grid/query/r18-stage.json'
parent=json.loads(parent_path.read_text());stage=json.loads((e/'source/r18-stage.json').read_text())
meta=json.loads((e/'source/metadata.json').read_text())
assert len(parent['files'])==197 and len(stage['files'])==198
assert stage['r54_query_control']['control_manifest_sha256']==sha(parent_path)
assert stage['r54_query_control']['parent_revision']==base and not stage['r54_query_control']['verifier_changed']
cargo='docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'
for name,digest in parent['files'].items():
    if name!=cargo:assert stage['files'][name]==digest,name
test='docs/research/v8-no-work-100-20260907/experiments/r54_query_control.rs'
assert set(stage['files'])-set(parent['files'])=={test}
assert stage['files'][test]==sha(root/'tools/r54_query_control.rs')
for name in ['crates/aspis-core/src/transcript.rs','crates/aspis-core/src/circle.rs']:
    assert stage['files'][name]==sha(repo/name)
assert meta['source_manifest_sha256']==sha(e/'source/r18-stage.json')
assert meta['fixture_sha256']==export['fixture_sha256']
assert meta['overflow_checks'] and not meta['sampler_law'] and not meta['full_privacy']
assert all(cmd['exit']==0 for cmd in meta['commands'])
cmd=meta['commands'][0]['command']
assert all(x in cmd for x in ['--release','--locked','--offline']) and cmd[cmd.index('--jobs')+1]=='2'
rust={name:metrics((e/f'source/{name}.log').read_text())for name in ['compile','query-control']}
log=(e/'source/query-control.log').read_text()
for field in ['cases=358','nonzero_cases=179','ood_cases=179',f'hash_calls={calls}',
    'complete_trace_bytes_equal=true','final_states_equal=true','results_errors_equal=true',
    'scripted_oracle=true','circle_word_refinement=false','universal_Rust_refinement=false',
    'source_probability=false','full_privacy=false']:assert field in log,field
hits=int(re.search(r'cache_hits=(\d+)',log).group(1));assert hits>0
receipt={'base_revision':base,'new_theorems':35,'new_axioms_audits':35,
    'final_cache_objects':286,'targets':results,'Rust':rust,
    'fixture_export':metrics((e/'replay/export.log').read_text()),
    'fixture_rows':358,'hash_calls':calls,'cache_hits':hits,
    'new_leaf_wall_seconds':round(sum(x['wall_seconds']for x in results.values()),2),
    'peak_success_rss_kib':max(x['peak_rss_kib']for x in results.values()),
    'resources':{'LeanHigh':'3G','LeanMax':'5G','RustHigh':'5G','RustMax':'7G',
        'MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':7},
    'bounded_wrapper_programs_and_laws':True,'canonical_word_to_exact_field_bridge':True,
    'circle_point_injective_and_outside_subfield':True,'complete_trace_replay_nonzero_OOD':True,
    'circle_Rust_inversion_refinement':False,'universal_Rust_refinement':False,
    'whole_source_prover_refinement':False,'source_challenge_joint_law':False,
    'numerical_source_privacy_bound':None,'full_privacy':False,'verifier_changed':False,
    'new_Rust_execution':True,'new_SBF_measurement':False}
pins={str((root/'lean'/(r['target_name']+'.lean')).relative_to(repo)):r['source_sha256']for r in records}
for path in [root/'tools'/n for n in ['run_r50_lean.py','run_r54_lean.py','run_r42_root_support.py',
    'run_r54_source.py','run_r53_replay.py','run_r54_replay.py','r54_query_control.rs','check_r54_evidence.py']]+[
    prior/'SOURCE_PINS.json',prior/'MANIFEST.json',parent_path,
    repo/'crates/aspis-core/src/transcript.rs',repo/'crates/aspis-core/src/circle.rs']:
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
     'fixture_rows','hash_calls','cache_hits','full_privacy','new_SBF_measurement')}},indent=2))
