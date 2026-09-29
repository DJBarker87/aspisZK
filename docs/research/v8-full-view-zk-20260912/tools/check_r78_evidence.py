#!/usr/bin/env python3
"""Audit actual circle-sampler value/error/state correspondence, not trace privacy."""
import argparse, hashlib, json, re, subprocess, sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r78-sampler-circle';parent=root/'evidence/r77-challenge-bridge'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def read(f):return json.loads(f.read_text())
subprocess.run([sys.executable,str(root/'tools/check_r77_evidence.py')],check=True)
reuse=json.loads(subprocess.check_output([sys.executable,str(root/'tools/generate_r78_closure.py')]))
assert reuse['status']=='PASS'
base='1eff875d763b8d7b591d12f9e5b5138de4fed250'
names=reuse['targets']+['SamplerCircleBridge']
records=read(e/'final/metadata.json')
assert len(records)==339 and records[:332]==read(parent/'final/metadata.json')
assert [r['target_name']for r in records[-7:]]==['AspisV8R19/'+n for n in names]
deps=read(e/'final/dependency-pins.json');assert len(deps)==344
assert read(e/'collection.json')['dependency_pins_verified']==344
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker,1)[1])==h,path
olddeps=read(parent/'final/dependency-pins.json')
for path,h in deps.items():
    if '/aeneas-full/' in path:assert olddeps[path]==h,path
# Freeze the old proof inputs independently of the namespace-reuse generator.
expected=[
 '28482f2eb063b94d6097edf8985f5bf80ea6ad6d645e695fabab7fe149c00016',
 '8d4c6e78a6a2c0ab3b9248eb63c704eae112973a1f0a7e9293d2c074528ba34d',
 '4fcf2a646c8c849838aa6925c082af20a681579f4a4e929e9ddda0e24019a37d',
 'f5272dfbdbf834b4be03168811cd1c9b8dd10a9cf838944fe52e045ff53da35d',
 '41eb6faf4c315378f28cfaa0c7911f70a97e0e78960ad3fd8fee54a27ac05830',
 '8eb34d45fb444dd6be48bb2e34108c25c7601b8e4beb490cf1a2431c6dda461c']
assert list(reuse['original_proof_pins'].values())==expected
res=read(e/'final/resources.json')
assert {k:res[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']}=={
    'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'}
metrics={};audits=[];formatter=[]
for r,n,count in zip(records[-7:],names,[13,2,10,20,15,12,5]):
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
assert len(audits)==77 and len(formatter)==4
assert all('.SamplerCircleBridge.'in n for n in formatter)
collision=(e/'transport/SamplerCircleTransport.log').read_text()
assert 'instDiscriminantCirclePointErrorIsize' in collision and 'Exit status: 1' in collision
assert 'Type mismatch' in (e/'bridge-a/SamplerCircleBridge.log').read_text()
receipt={'base_revision':base,'compiled_targets':7,'cached_targets':332,'theorems':audits,
    'metrics':metrics,'new_axioms':0,'standard_axioms_only':False,
    'inherited_opaque_type':'core.fmt.Formatter','formatter_dependent_theorems':formatter,
    'namespace_reuse':reuse,'original_extractions_modified':False,
    'source_circle_value_error_state_bridge':True,'outer_retry_limit':3,
    'successful_source_points_canonical_on_circle_outside_CM31':True,
    'bridge_backend':'explicit total deterministic hashv adapter for arbitrary H',
    'independent_hash_answers_assumed':False,'concrete_SHA_ideality_proved':False,
    'complete_source_oracle_trace_correspondence':False,
    'runtime_changed':False,'cu':[1495663,1497050],'actual_1M_gate_passed':False,
    'full_privacy':False,'full_soundness':False,
    'first_remaining':'Prove source-observer/hash-query-history correspondence for the complete sampler, separately from value/error/state equality. Then instantiate its retained coherent memoized-oracle laws in the actual full transcript; no global privacy or loss bound follows from this bridge alone.'}
files=[root/'lean/AspisV8R19'/(n+'.lean')for n in names]
files += [root/n for n in reuse['original_proof_pins']]
files += [root/'lean/AspisR72Sampler'/(n+'.lean')for n in ['Types','Funs']]
files += [root/'lean/AspisV8R19'/(n+'.lean')for n in ['SamplerOuterExecution','SamplerChallengeBridge',
    'SamplerCirclePolicy','BoundedSamplerWrapper','SamplerFieldDecode']]
files += [root/'tools'/n for n in ['check_r78_evidence.py','collect_r78_evidence.py','run_r78_lean.py',
    'generate_r78_closure.py','run_r68_lean.py','run_r64_lean.py','run_r63_lean.py','check_r77_evidence.py']]
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
