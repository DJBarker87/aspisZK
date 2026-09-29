#!/usr/bin/env python3
"""Audit checked-source inverse execution; keep full privacy gates explicit."""
import argparse, hashlib, json, re
from pathlib import Path
from audit_r64_source import check_current
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r64-guarded-execution'
base='a40fb23673ab80c67e99c06bf156f338b12b2a2e'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(path,count=None):
    s=path.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s
    assert not re.search(r'^.*error(?:\[|\(|:)',s,re.M) and 'sorryAx' not in s
    if count is not None:
        ax=re.findall(r'depends on axioms: \[([^]]*)\]',s)
        assert len(ax)+s.count('does not depend on any axioms')==count
        for x in ax:assert set(x.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s).group(1).split(':')
    return {'exit':0,'swaps':0,'axioms_audited':count,
      'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
      'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s).group(1))}
records=json.loads((e/'lean/metadata.json').read_text());assert len(records)==303;pins={}
for r in records:
    path=root/'lean'/(r['target_name']+'.lean')
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0' and sha(path)==r['source_sha256']
    pins[str(path.relative_to(repo))]=sha(path)
results={}
for name,count in [('CanonicalProduct',9),('GuardedFieldSlice',0),('GuardedM31Execution',6),('GuardedInverseExecution',8)]:
    r=next(r for r in records if r['target_name']=='AspisV8R19/'+name)
    assert r['base_revision']==base and r['command'][1:3]==['env','lean']
    src=(root/'lean/AspisV8R19'/(name+'.lean')).read_text()
    assert len(re.findall(r'^theorem ',src,re.M))==count
    assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',src)
    results[name]=metrics(e/'lean'/(name+'.log'),count)
checked=e/'extraction/checked';wrapping=e/'extraction/wrapping'
stage=root/'evidence/r63-generated-inverse/source';kit=root/'tools/r64-field-extraction'
slice=root/'lean/AspisV8R19/GuardedFieldSlice.lean'
audit=check_current(checked,slice,stage,kit)
assert audit==json.loads((e/'source-audit.json').read_text())
for n,h in json.loads((wrapping/'pins.json').read_text()).items():assert sha(wrapping/n)==h
assert 'wrapping_mul' in (wrapping/'generated/AspisR64Field/Funs.lean').read_text()
assert 'wrapping_' not in (checked/'generated/AspisR64Field/Funs.lean').read_text()
try:check_current(wrapping,slice,stage,kit)
except AssertionError:pass
else:raise AssertionError('accepted the mismatched release profile')
for name in ['field.rs','r23_width.rs','r24_guarded_qm.rs','r25_checked_dot.rs']:
    assert sha(checked/'source'/name)==sha(wrapping/'source'/name)
environment=root/'evidence/r62-ordinary/gather-checked/r24-sbf-a/environment.json'
assert json.loads(environment.read_text())['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
extraction={}
for variant in ['checked','wrapping']:
    extraction[variant]={n:metrics(e/'extraction'/variant/(n+'.log')) for n in ['lock','extract','translate']}
for name in ['mul-a','mul-b','inverse-a']:
    r=json.loads((e/'development'/(name+'.json')).read_text());assert r['exit']==1
    assert '\tExit status: 1' in (e/'development'/(name+'.log')).read_text()
deps=json.loads((e/'lean/dependency-pins.json').read_text());assert len(deps)==141
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker)[1])==h
for n in ['run_r63_lean.py','run_r64_lean.py','audit_r64_source.py','extract_r64_field.py','collect_r64_execution.py','check_r64_execution.py']:
    path=root/'tools'/n;pins[str(path.relative_to(repo))]=sha(path)
for path in [*kit.iterdir(),environment,stage/'r18-stage.json',root/'evidence/r62-ordinary/receipt.json']:
    if path.is_file():pins[str(path.relative_to(repo))]=sha(path)
receipt={'base_revision':base,'new_execution_theorems':14,'retained_arithmetic_theorems_replayed':9,
 'axioms_audited':23,'results':results,'extraction':extraction,'cache_targets':303,'runtime_dependency_pins':141,
 'source_files_unchanged':4,'selected_stage_pins':197,'exact_generated_declarations':9,'generated_negative_mutations':9,
 'mismatched_wrapping_extraction_rejected':True,'selected_overflow_checked_profile':True,
 'all_U32_generated_multiplication_Result_equivalence':True,'generated_inverse_Result_equivalence':True,
 'canonical_nonzero_generated_inverse_correct':True,'zero_assertion_failure_preserved':True,
 'verified_extraction_compiler':False,'complete_current_field_tower':False,'full_privacy':False,'full_soundness':False,
 'source_privacy_numerical_bound':None,'runtime_changed':False,'new_SBF_run':False,'retained_cu':[1497377,1498764],
 'actual_1M_gate_passed':False,'first_remaining':'actual CM31/QM31 norm, negation, equality and try_inv composition, then circle and bounded sampler observer',
 'resources':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':7}}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f) for f in sorted(e.rglob('*')) if f.is_file() and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt and json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text())
assert set(manifest)=={str(f.relative_to(e)) for f in e.rglob('*') if f.is_file() and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','artifacts':len(manifest),'pins':len(pins),'new_execution_theorems':14,
 'axioms_audited':23,'full_privacy':False,'retained_cu':receipt['retained_cu']},indent=2))
