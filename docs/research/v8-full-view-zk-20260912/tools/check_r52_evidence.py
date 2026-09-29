#!/usr/bin/env python3
"""Validate R52 exact memoized-oracle laws and retained source evidence pins."""
import argparse
import hashlib
import json
import re
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r52-memoized-oracle-law'
base='55f6f65530e6b1dbccd9c4ea23d82268974d45f9'
checks=[('b','OracleResampling',6,7),('d','MemoizedProgramLaw',9,9),
        ('e','OracleProgramOps',4,4),('g','OracleFiniteSupport',7,7),
        ('j','SourceOraclePrograms',8,8),('k','StoppingOracleProgram',4,4),
        ('l','OracleLawControls',6,6)]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(log,audits):
    assert '\tExit status: 0' in log and '\tSwaps: 0' in log
    assert 'error:' not in log and 'sorryAx' not in log
    axioms=re.findall(r'depends on axioms: \[([^]]*)\]',log)
    assert len(axioms)+log.count('does not depend on any axioms')==audits
    for ax in axioms:
        assert set(re.sub(r'\s','',ax).split(','))<={'propext','Classical.choice','Quot.sound'}
    ts=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':')
    return {'exit':0,'swaps':0,'axioms_audited':audits,
        'wall_seconds':round(sum(float(t)*60**i for i,t in enumerate(reversed(ts))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1))}
records=json.loads((e/'lean-l/metadata.json').read_text());assert len(records)==271
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(root/'lean'/(r['target_name']+'.lean'))==r['source_sha256']
prior=root/'evidence/r51-duplex-first-hit'
for name,digest in json.loads((prior/'SOURCE_PINS.json').read_text()).items():
    assert sha(repo/name)==digest,name
for name,digest in json.loads((prior/'MANIFEST.json').read_text()).items():
    assert sha(prior/name)==digest,name
results={}
for letter,name,theorems,audits in checks:
    log=(e/f'lean-{letter}/{name}.log').read_text();result=metrics(log,audits)
    result['theorems']=theorems;results[name]=result
    src=(root/'lean/AspisV8R19'/(name+'.lean')).read_text()
    assert len(re.findall(r'^theorem ',src,re.M))==theorems
    assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth|norm_num)\b',src)
    r=next(r for r in records if r['target_name']=='AspisV8R19/'+name)
    assert r['base_revision']==base and f'/aspis-r52-lean-20260929-{letter}/lib/' in r['command'][6]
for letter,name in [('a','OracleResampling'),('c','MemoizedProgramLaw'),('f','OracleFiniteSupport'),
                    ('h','SourceOraclePrograms'),('i','SourceOraclePrograms'),('k','OracleLawControls')]:
    assert '\tExit status: 1' in (e/f'lean-{letter}/{name}.log').read_text()
metrics((e/'lean-c/Table.log').read_text(),3)
receipt={'base_revision':base,'new_theorems':44,'new_axioms_audits':45,
    'final_cache_objects':271,'targets':results,
    'new_leaf_wall_seconds':round(sum(v['wall_seconds']for v in results.values()),2),
    'peak_success_rss_kib':max(v['peak_rss_kib']for v in results.values()),
    'resources':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128,
        'max_simultaneous_reservation_gib':5},
    'complete_oracle_equals_first_read_only_interpreter':True,
    'cache_hits_replay_answers':True,'finite_all_branches_support':True,
    'arbitrary_byte_addresses':True,'complete_query_trace_retained':True,
    'bounded_stopping_and_exhaustion_retained':True,'source_primitives_bound':True,
    'all_source_samplers_compiled_to_program':False,'whole_source_prover_refinement':False,
    'source_challenge_joint_law':False,'numerical_source_privacy_bound':None,
    'Rust_extraction':False,'full_privacy':False,'verifier_changed':False,
    'new_Rust_execution':False,'new_SBF_measurement':False}
pins={str((root/'lean'/(r['target_name']+'.lean')).relative_to(repo)):r['source_sha256']for r in records}
for path in [root/'tools/run_r50_lean.py',root/'tools/run_r52_lean.py',root/'tools/check_r52_evidence.py',
             prior/'SOURCE_PINS.json',prior/'MANIFEST.json',repo/'crates/aspis-core/src/transcript.rs']:
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
