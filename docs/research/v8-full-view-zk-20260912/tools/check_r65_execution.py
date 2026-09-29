#!/usr/bin/env python3
"""Audit the source-generated CM31 milestone, not global privacy/security."""
import argparse, hashlib, json, re
from pathlib import Path
from audit_r65_source import check_current
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r65-complex-inverse'
base='70b2494f91a4dae94059f96900232dac5a611ccc'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(path,count=None):
    s=path.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s
    assert not re.search(r'^.*error(?:\[|\(|:)',s,re.M) and 'sorryAx' not in s
    if count is not None:
        ax=re.findall(r'depends on axioms: \[([^]]*)\]',s)
        assert len(ax)+s.count('does not depend on any axioms')==count
        for x in ax:assert set(re.sub(r'\s','',x).split(','))<={'propext','Classical.choice','Quot.sound'}
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s).group(1).split(':')
    return {'exit':0,'swaps':0,'axioms_audited':count,
      'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
      'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s).group(1))}
records=json.loads((e/'lean/metadata.json').read_text());assert len(records)==306;pins={}
for r in records:
    path=root/'lean'/(r['target_name']+'.lean')
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0' and sha(path)==r['source_sha256']
    pins[str(path.relative_to(repo))]=sha(path)
results={}
for name,count in [('ComplexFieldSlice',0),('ComplexBaseExecution',15),('ComplexInverseExecution',10)]:
    r=next(r for r in records if r['target_name']=='AspisV8R19/'+name)
    assert r['base_revision']==base and r['command'][1:3]==['env','lean']
    assert '-j1' in r['command'] and '-M4500' in r['command']
    src=(root/'lean/AspisV8R19'/(name+'.lean')).read_text()
    assert len(re.findall(r'^(?:@\[simp\] )?theorem ',src,re.M))==count
    assert not re.search(r'\b(sorry|axiom|native_decide)\b',src)
    results[name]=metrics(e/'lean'/(name+'.log'),count)
extraction=e/'extraction';stage=root/'evidence/r63-generated-inverse/source';kit=root/'tools/r65-field-extraction'
audit=check_current(extraction,root/'lean/AspisV8R19/ComplexFieldSlice.lean',stage,kit)
assert audit==json.loads((e/'source-audit.json').read_text())
assert 'wrapping_' not in (extraction/'generated/AspisR65Field/Funs.lean').read_text()
environment=root/'evidence/r62-ordinary/gather-checked/r24-sbf-a/environment.json'
assert json.loads(environment.read_text())['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
extract_metrics={n:metrics(extraction/(n+'.log')) for n in ['lock','extract','translate']}
for name in ['base-a','base-b','inverse-a']:
    r=json.loads((e/'development'/(name+'.json')).read_text());assert r['exit']==1 and r['base_revision']==base
    assert '\tExit status: 1' in (e/'development'/(name+'.log')).read_text()
deps=json.loads((e/'lean/dependency-pins.json').read_text());assert len(deps)==168
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker)[1])==h
resources=json.loads((e/'lean/resources.json').read_text())
assert resources['memory.high']==str(5*2**30) and resources['memory.max']==str(7*2**30)
assert resources['memory.swap.max']=='0' and resources['pids.max']=='128'
for n in ['run_r63_lean.py','run_r64_lean.py','run_r65_lean.py','audit_r65_source.py',
          'extract_r64_field.py','extract_r65_field.py','collect_r65_execution.py','check_r65_execution.py']:
    path=root/'tools'/n;pins[str(path.relative_to(repo))]=sha(path)
for path in [*kit.iterdir(),environment,stage/'r18-stage.json',root/'evidence/r62-ordinary/receipt.json']:
    if path.is_file():pins[str(path.relative_to(repo))]=sha(path)
receipt={'base_revision':base,'new_theorems':25,'axioms_audited':25,'results':results,
 'extraction':extract_metrics,'cache_targets':306,'runtime_dependency_pins':168,
 'source_files_unchanged':4,'selected_stage_pins':197,'exact_generated_declarations':14,
 'generated_negative_mutations':8,'selected_overflow_checked_profile':True,
 'canonical_CM31_inverse_generated_execution':True,'zero_assertion_failure_iff_zero_limbs':True,
 'actual_M31_backend_instantiated':True,'new_cryptographic_or_nonsquare_assumption':False,
 'verified_extraction_compiler':False,'complete_current_field_tower':False,'full_privacy':False,'full_soundness':False,
 'source_privacy_numerical_bound':None,'runtime_changed':False,'new_SBF_run':False,'retained_cu':[1497377,1498764],
 'actual_1M_gate_passed':False,
 'first_remaining':'actual optimized CM31 square/mul/sub and QM31 zero/try_inv composition, then circle and bounded sampler observer',
 'resources':resources}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f) for f in sorted(e.rglob('*')) if f.is_file() and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt and json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text())
assert set(manifest)=={str(f.relative_to(e)) for f in e.rglob('*') if f.is_file() and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','artifacts':len(manifest),'pins':len(pins),'new_theorems':25,
 'axioms_audited':25,'full_privacy':False,'retained_cu':receipt['retained_cu']},indent=2))
