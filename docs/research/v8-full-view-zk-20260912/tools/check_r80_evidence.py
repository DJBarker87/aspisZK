#!/usr/bin/env python3
"""Audit complete instrumented QM31 query/value/state correspondence."""
import argparse, hashlib, json, re, subprocess, sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r80-qm31-observer';parent=root/'evidence/r79-sampler-observer'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def read(f):return json.loads(f.read_text())
subprocess.run([sys.executable,str(root/'tools/check_r79_evidence.py')],check=True)
base='8b4d9f417497961530e818419156ae5968c7ef31'
names=['SamplerObservedInnerLoop','SamplerObservedLimbBridge','SamplerObservedLimbLoop',
       'SamplerObservedWriteback','SamplerObservedChallenge','SamplerObservedProgram']
records=read(e/'final/metadata.json')
assert len(records)==350 and records[:344]==read(parent/'final/metadata.json')
assert [r['target_name']for r in records[-6:]]==['AspisV8R19/'+n for n in names]
deps=read(e/'final/dependency-pins.json');assert len(deps)==318
assert read(e/'collection.json')['dependency_pins_verified']==318
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker,1)[1])==h,path
olddeps=read(parent/'final/dependency-pins.json')
for path,h in deps.items():
    if '/aeneas-full/' in path:assert olddeps[path]==h,path
res=read(e/'final/resources.json')
assert {k:res[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']}=={
    'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'}
metrics={};audits=[];formatter=[]
for r,n,count in zip(records[-6:],names,[3,5,3,1,4,3]):
    src=root/'lean'/(r['target_name']+'.lean');s=src.read_text()
    assert r['source_sha256']==sha(src) and r['base_revision']==base and r['exit']==0
    assert r['toolchain']=='leanprover/lean4:v4.32.0'
    assert '-j1' in r['command'] and '-M4500' in r['command']
    assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',s)
    assert 'maxHeartbeats' not in s
    log=(e/'final'/(n+'.log')).read_text()
    assert 'sorryAx' not in log and 'error:' not in log and 'warning:' not in log
    got=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
    assert len(got)==count
    for name,axs in got:
        axset={v.strip()for v in axs.split(',')}
        assert axset<={'propext','Classical.choice','Quot.sound','core.fmt.Formatter'}
        audits.append(name)
        if 'core.fmt.Formatter' in axset:formatter.append(name)
    assert re.findall(r'\tExit status: (\d+)',log)==['0']
    assert re.findall(r'\tSwaps: (\d+)',log)==['0']
    wall=re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[0]
    metrics[n]={'exit':0,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(wall.split(':')))),2),
                'peak_rss_kib':int(re.findall(r'Maximum resident set size \(kbytes\): (\d+)',log)[0])}
assert len(audits)==19 and len(formatter)==16
receipt={'base_revision':base,'compiled_targets':6,'cached_targets':344,'theorems':audits,
    'metrics':metrics,'new_axioms':0,'standard_axioms_only':False,
    'inherited_opaque_type':'core.fmt.Formatter','formatter_dependent_theorems':formatter,
    'original_extractions_modified':False,'instrumentation_changed':False,
    'instrumentation_checker_formally_certified':False,
    'complete_instrumented_QM31_value_error_state_trace_matches_program':True,
    'instrumented_QM31_erasure_matches_original_under_adapter':True,
    'internal_hash_pointer_excluded_from_observed_view':True,
    'complete_instrumented_circle_trace_theorem':False,
    'complete_source_observer_refinement':False,'backend_failure_prefix_trace_retained':False,
    'adapter':'explicit total deterministic hashv adapter for arbitrary H',
    'independent_hash_answers_assumed':False,'concrete_SHA_ideality_proved':False,
    'runtime_changed':False,'cu':[1495663,1497050],'actual_1M_gate_passed':False,
    'full_privacy':False,'full_soundness':False,
    'first_remaining':'Compose instrumented secure-circle outer retries with the proved exact circle map and QM31 observed program, retaining both exhaustion errors and advanced state. Then justify the complete source observer and actual coherent-oracle experiment; R79 instrumentation remains an explicit non-certified trust boundary.'}
files=[root/'lean/AspisV8R19'/(n+'.lean')for n in names]
files += [root/'lean/AspisV8R19'/(n+'.lean')for n in ['SamplerObservedSource','SamplerObservation',
    'SamplerObservedSqueeze','SamplerObservedInnerStep','SamplerLimbBridge','SamplerWriteback',
    'SamplerChallengeBridge','QM31SamplerProgram','QM31SamplerInvariants']]
files += [root/'tools'/n for n in ['check_r80_evidence.py','collect_r80_evidence.py','run_r80_lean.py',
    'generate_r79_observer.py','run_r68_lean.py','run_r64_lean.py','run_r63_lean.py','check_r79_evidence.py']]
files += [parent/'MANIFEST.json',parent/'SOURCE_PINS.json',parent/'receipt.json']
pins={str(f.relative_to(repo)):sha(f)for f in files}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert read(e/'receipt.json')==receipt and read(e/'SOURCE_PINS.json')==pins
manifest=read(e/'MANIFEST.json')
assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'audit':'PASS_SCOPED','theorems':len(audits),'metrics':metrics,
    'inherited_opaque_type':'core.fmt.Formatter','full_privacy':False,'artifacts':len(manifest)},indent=2))
