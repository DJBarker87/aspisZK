#!/usr/bin/env python3
"""Audit actual complete QM31 challenge value/state model correspondence."""
import argparse, hashlib, json, re, subprocess, sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r77-challenge-bridge';parent=root/'evidence/r76-limb-bridge'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def read(f):return json.loads(f.read_text())
subprocess.run([sys.executable,str(root/'tools/check_r76_evidence.py')],check=True)
base='8b8a8e43a498cbf294e9e4f132a9dc5a22ede2fc'
names=['SamplerWriteback','SamplerChallengeBridge']
records=read(e/'final/metadata.json')
assert len(records)==332 and records[:330]==read(parent/'final/metadata.json')
assert [r['target_name']for r in records[-2:]]==['AspisV8R19/'+n for n in names]
deps=read(e/'final/dependency-pins.json');assert len(deps)==307
assert read(e/'collection.json')['dependency_pins_verified']==307
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
for r,n,count in zip(records[-2:],names,[3,5]):
    src=root/'lean'/(r['target_name']+'.lean');s=src.read_text()
    assert r['source_sha256']==sha(src) and r['base_revision']==base and r['exit']==0
    assert r['toolchain']=='leanprover/lean4:v4.32.0'
    assert '-j1' in r['command'] and '-M4500' in r['command']
    assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',s)
    assert 'maxHeartbeats' not in s
    log=(e/'final'/(n+'.log')).read_text()
    assert 'sorryAx' not in log and 'error:' not in log
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
assert len(formatter)==6
receipt={'base_revision':base,'compiled_targets':2,'cached_targets':330,'theorems':audits,
    'metrics':metrics,'new_axioms':0,'standard_axioms_only':False,
    'inherited_opaque_type':'core.fmt.Formatter','formatter_dependent_theorems':formatter,
    'source_mutable_writeback_matches_model':True,'complete_QM31_value_state_bridge':True,
    'source_exhaustion_state_matches_model':True,'source_successful_output_canonical':True,
    'bridge_backend':'explicit total deterministic hashv adapter for arbitrary H',
    'independent_hash_answers_assumed':False,'concrete_SHA_ideality_proved':False,
    'complete_source_oracle_trace_correspondence':False,'circle_outer_model_composition':False,
    'runtime_changed':False,'cu':[1495663,1497050],'actual_1M_gate_passed':False,
    'full_privacy':False,'full_soundness':False,
    'first_remaining':'Establish source sampler observer/hash-query trace correspondence and transport the proved circle map into the actual R72 sampler namespace, then compose the full circle sampler including outer retries. Value/state equivalence alone is not trace equivalence.'}
files=[root/'lean/AspisV8R19'/(n+'.lean')for n in names]
files += [root/'lean/AspisR72Sampler'/(n+'.lean')for n in ['Types','Funs']]
files += [root/'lean/AspisV8R19'/(n+'.lean')for n in ['SamplerLimbLoop','SamplerLimbBridge','QM31SamplerInvariants','QM31SamplerProgram','SqueezeOracleBridge']]
files += [root/'tools'/n for n in ['check_r77_evidence.py','collect_r77_evidence.py','run_r77_lean.py',
    'run_r68_lean.py','run_r64_lean.py','run_r63_lean.py','check_r76_evidence.py']]
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
