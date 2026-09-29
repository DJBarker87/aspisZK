#!/usr/bin/env python3
"""Verify generated-loop proof evidence without promoting it to current/full privacy."""
import argparse, hashlib, json, re
from pathlib import Path
from audit_r63_source import check
from audit_r60_source import audit
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r63-generated-inverse'
base='491ccd3d42e2e07ff2c04cb6dd17c7ea20269ed0'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((e/'lean/metadata.json').read_text());assert len(records)==299
pins={}
for r in records:
    path=root/'lean'/(r['target_name']+'.lean')
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(path)==r['source_sha256'];pins[str(path.relative_to(repo))]=sha(path)
results={}
for name,count in [('InverseFieldSlice',0),('InverseRuntimeMul',21),('GeneratedInverseLoop',9)]:
    r=next(r for r in records if r['target_name']=='AspisV8R19/'+name)
    assert r['base_revision']==base and r['command'][1:3]==['env','lean']
    text=(e/'lean'/(name+'.log')).read_text()
    assert '\tExit status: 0' in text and '\tSwaps: 0' in text and 'sorryAx' not in text
    assert not re.search(r'^.*error(?:\[|\(|:)',text,re.M)
    axioms=re.findall(r'depends on axioms: \[([^]]*)\]',text)
    assert len(axioms)+text.count('does not depend on any axioms')==count
    for ax in axioms:assert set(ax.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
    source=(root/'lean/AspisV8R19'/(name+'.lean')).read_text()
    assert len(re.findall(r'^(?:@\[simp\] )?theorem ',source,re.M))==count
    assert not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',source)
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',text).group(1).split(':')
    results[name]={'exit':0,'swaps':0,'axioms_audited':count,
      'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
      'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',text).group(1))}
source=check(e/'source/generated',root/'lean/AspisV8R19/InverseFieldSlice.lean',e/'source/selected-field.rs',root/'lean/AspisV8R19/InverseChain.lean')
assert source==json.loads((e/'source/audit.json').read_text())
assert source['selected_M31_differs_from_generated'] and not source['selected_M31_universal_execution_bridge_proved']
local=audit((repo/'crates/aspis-core/src/field.rs').read_text(),(root/'lean/AspisV8R19/InverseChain.lean').read_text())
assert local['schedule']==source['rust_schedule']['schedule']
stage=json.loads((e/'source/r18-stage.json').read_text());assert len(stage['files'])==197
assert sha(e/'source/selected-field.rs')==stage['files']['crates/aspis-core/src/field.rs']
assert sha(e/'source/r18-stage.json')==sha(root/'evidence/r62-ordinary/gather-checked/r18-stage.json')
deps=json.loads((e/'lean/dependency-pins.json').read_text());assert len(deps)==137
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker)[1])==h
assert any(n.endswith('/Aeneas/Std/Core/Iter.lean') for n in deps)
assert any(n.endswith('/Aeneas/Std/Core/Iter.olean') for n in deps)
for n in ['run_r63_lean.py','audit_r63_source.py','collect_r63_evidence.py','check_r63_evidence.py','check_r17_field_slice.py','audit_r60_source.py']:
    path=root/'tools'/n;pins[str(path.relative_to(repo))]=sha(path)
for path in [repo/'crates/aspis-core/src/field.rs',root/'evidence/r62-ordinary/receipt.json']:
    pins[str(path.relative_to(repo))]=sha(path)
receipt={'base_revision':base,'compiled_leaves':3,'new_loop_bridge_theorems':9,'replayed_full_runtime_support_theorems':21,
  'axioms_audited':30,'results':results,'cache_targets':299,'runtime_dependency_pins':137,
  'generated_declarations_byte_identical':8,'generated_negative_mutations_rejected':8,
  'generated_canonical_inverse_execution_proved':True,'generated_zero_assertion_failure_proved':True,
  'optimized_R62_M31_execution_bridge':False,'complete_Rust_tower_refinement':False,
  'full_privacy':False,'full_soundness':False,'numerical_source_privacy_bound':None,
  'runtime_changed':False,'new_SBF_run':False,'retained_cu':[1497377,1498764],'actual_1M_gate_passed':False,
  'first_remaining':'R62 guarded one-fold M31 execution equivalence, then word-level norm/negation/equality/try_inv composition',
  'resources':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':7}}
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
print(json.dumps({'status':'PASS','artifacts':len(manifest),'pins':len(pins),'axioms_audited':30,
  'optimized_R62_M31_execution_bridge':False,'full_privacy':False,'retained_cu':receipt['retained_cu']},indent=2))
