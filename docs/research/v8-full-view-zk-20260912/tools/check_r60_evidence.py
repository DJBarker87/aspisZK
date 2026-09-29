#!/usr/bin/env python3
"""Check symbolic inversion/circle boundary without promoting it to extraction."""
import argparse,hashlib,json,re
from pathlib import Path
from audit_r60_source import audit,function,clean
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r60-inverse-chain'
base='eb51ef6ea5be51585ee40da75a86567b92c1575e'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(p,count):
    s=p.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s,p
    assert not re.search(r'^.*error(?:\[|\(|:)',s,re.M) and 'sorryAx' not in s,p
    ax=re.findall(r'depends on axioms: \[([^]]*)\]',s)
    assert len(ax)+s.count('does not depend on any axioms')==count
    for x in ax:assert set(x.replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s).group(1).split(':')
    return {'exit':0,'swaps':0,'axioms_audited':count,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s).group(1))}
records=json.loads((e/'lean/metadata.json').read_text());assert len(records)==295;pins={}
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    path=root/'lean'/(r['target_name']+'.lean');assert sha(path)==r['source_sha256'];pins[str(path.relative_to(repo))]=sha(path)
results={}
for n,count in [('InverseChain',10),('NormInverse',13)]:
    r=next(r for r in records if r['target_name']=='AspisV8R19/'+n);assert r['base_revision']==base
    results[n]=metrics(e/'lean'/(n+'.log'),count)
    src=(root/'lean/AspisV8R19'/(n+'.lean')).read_text()
    assert len(re.findall(r'^theorem ',src,re.M))==count and not re.search(r'\b(sorry|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',src)
for n in ['RawReducerNat','RawReducer']:results[n]=metrics(e/'lean'/(n+'.log'),4)
for folder,n in [('b','InverseChain'),('c','NormInverse'),('e','NormInverse')]:
    log=(e/f'failures/{folder}-{n}.log').read_text();r=json.loads((e/f'failures/{folder}-{n}.json').read_text())
    assert '\tExit status: 1' in log and r['exit']==1
field=e/'source/crates/aspis-core/src/field.rs';circle=e/'source/crates/aspis-core/src/circle.rs'
m=json.loads((e/'source/r18-stage.json').read_text());parent=root/'evidence/r59-partial-dot/r18-stage.json'
assert sha(e/'source/r18-stage.json')==sha(parent) and len(m['files'])==195
assert sha(field)==m['files']['crates/aspis-core/src/field.rs']
assert sha(circle)==sha(repo/'crates/aspis-core/src/circle.rs')
lean=root/'lean/AspisV8R19/InverseChain.lean'
source=audit(field.read_text(),lean.read_text());source.update(field_sha256=sha(field),lean_sha256=sha(lean))
assert source==json.loads((e/'source/audit.json').read_text()) and source['negative_mutations_rejected']==5
local=audit((repo/'crates/aspis-core/src/field.rs').read_text(),lean.read_text())
assert local['schedule']==source['schedule']
# Freeze the exact norm/conjugate/error-order source bodies as reviewed; no
# implication that this text audit establishes word-level execution.
norm={}
for key,needle in [('cm31','pub fn inv_with(self, inverse: fn(M31) -> M31) -> CM31'),('qm31','pub fn try_inv(self) -> Option<QM31>')]:
    actual=clean(function(field.read_text(),needle));expected=clean(function((repo/'crates/aspis-core/src/field.rs').read_text(),needle))
    assert actual==expected;norm[key]=hashlib.sha256(actual.encode()).hexdigest()
pre=json.loads((e/'cache-preflight.json').read_text());assert pre['old_reducer_sha256']!=pre['current_reducer_sha256']
assert pre['current_reducer_sha256']==sha(root/'lean/AspisV8R17/RawReducer.lean') and pre['old_unsplit_object_not_reused']
receipt={'base_revision':base,'new_theorems':23,'new_axioms_audits':23,'results':results,'cache_objects':295,
    'source_chain_multiplications':38,'source_schedule_bindings':9,'source_negative_mutations':5,'norm_source_body_hashes':norm,
    'mathematical_chain_and_norm_correct':True,'chain_based_circle_program_law':True,
    'universal_Rust_loop_refinement':False,'universal_Rust_field_refinement':False,'full_privacy':False,'full_soundness':False,
    'numerical_source_privacy_bound':None,'verifier_changed':False,'new_Rust_or_SBF_run':False,
    'retained_cu':[1516838,1518195],'actual_1M_gate_passed':False,
    'resources':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':5}}
for path in [root/'tools'/n for n in ['run_r60_lean.py','audit_r60_source.py','collect_r60_evidence.py','check_r60_evidence.py','run_r50_lean.py']]+[
    parent,root/'evidence/r59-partial-dot/receipt.json',repo/'crates/aspis-core/src/field.rs',repo/'crates/aspis-core/src/circle.rs']:
    pins[str(path.relative_to(repo))]=sha(path)
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');(e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt and json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text());assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','artifacts':len(manifest),'pins':len(pins),'new_theorems':23,
    'universal_Rust_field_refinement':False,'full_privacy':False,'retained_cu':receipt['retained_cu']},indent=2))
