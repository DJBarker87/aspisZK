#!/usr/bin/env python3
"""Audit the arithmetic-only leaf; never label it a generated execution proof."""
import argparse, hashlib, json, re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r64-canonical-product'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((e/'metadata.json').read_text());assert len(records)==2
results={};pins={}
for r in records:
    name=r['target_name'];src=root/'lean'/(name+'.lean')
    assert sha(src)==r['source_sha256'] and r['exit']==0
    assert r['toolchain']=='leanprover/lean4:v4.32.0'
    assert r['mathlib_revision']=='81a5d257c8e410db227a6665ed08f64fea08e997'
    assert r['base_revision']=='2a9d914ff615bfc9d046399074d05b8164791412'
    assert r['command'][1:3]==['env','lean'] and '-M1024' in r['command']
    count=9 if name.endswith('CanonicalProduct') else 4
    log=(e/(Path(name).name+'.log')).read_text()
    assert not re.search(r'^.*error(?:\[|\(|:)',log,re.M) and 'sorryAx' not in log
    ax=re.findall(r'depends on axioms: \[([^]]*)\]',log)
    assert len(ax)+log.count('does not depend on any axioms')==count
    for x in ax:assert set(x.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
    assert int(re.search(r'^\s*(\d+)\s+swaps$',log,re.M).group(1))==0
    wall=float(re.search(r'^\s*([\d.]+) real',log,re.M).group(1))
    rss=int(re.search(r'^\s*(\d+)\s+maximum resident set size$',log,re.M).group(1))
    assert rss < 1024**3
    results[name]={'exit':0,'wall_seconds':wall,'peak_rss_bytes':rss,'swaps':0,'axioms_audited':count}
    pins[str(src.relative_to(repo))]=sha(src)
source=(root/'lean/AspisV8R19/CanonicalProduct.lean').read_text()
assert len(re.findall(r'^theorem ',source,re.M))==9
assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',source)
for n in ['run_r64_local_bound.py','check_r64_bound_evidence.py']:
    path=root/'tools'/n;pins[str(path.relative_to(repo))]=sha(path)
selected=root/'evidence/r63-generated-inverse/source/selected-field.rs'
stage=root/'evidence/r63-generated-inverse/source/r18-stage.json'
assert sha(selected)==json.loads(stage.read_text())['files']['crates/aspis-core/src/field.rs']
for path in [selected,stage,root/'evidence/r63-generated-inverse/receipt.json',root/'evidence/r62-ordinary/receipt.json']:
    pins[str(path.relative_to(repo))]=sha(path)
receipt={'base_revision':'2a9d914ff615bfc9d046399074d05b8164791412',
 'new_theorems':9,'axioms_audited':9,'retained_dependency_axioms_audited':4,'results':results,
 'guarded_Nat_formula_equal_for_all_U32_values':True,'general_u62_counterexample_proved':True,
 'fresh_extraction_artifacts_retrieved':False,'generated_optimized_word_execution_proved':False,
 'new_privacy_or_soundness_claim':False,'full_privacy':False,'runtime_changed':False,'new_SBF_run':False,
 'retained_cu':[1497377,1498764],'actual_1M_gate_passed':False,
 'first_remaining':'retrieve/audit completed R64 extraction; connect actual generated word operations to this arithmetic and R63 inverse loop',
 'resources':{'host':'laptop','focused_Nat_only':True,'lean_heap_mib':1024,'workers':1,'cpu_soft_seconds':30,'cpu_hard_seconds':35,'wall_limit_seconds':60,'cold_dependency_build':False}}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f) for f in sorted(e.rglob('*')) if f.is_file() and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt
assert json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text())
assert set(manifest)=={str(f.relative_to(e)) for f in e.rglob('*') if f.is_file() and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','new_theorems':9,'artifacts':len(manifest),'pins':len(pins),
 'generated_optimized_word_execution_proved':False,'full_privacy':False},indent=2))
