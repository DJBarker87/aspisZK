#!/usr/bin/env python3
"""Check the source-locked generated canonical product proof, not full privacy."""
import argparse, hashlib, json, re, subprocess, sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r70-product';parent=root/'evidence/r69-explicit-source'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def read(f):return json.loads(f.read_text())
subprocess.run([sys.executable,str(root/'tools/check_r69_evidence.py')],check=True)
base='851c10072a74fff8523b8817d791153128cf920e'
names=['ExplicitWord','ProductExecution','ProductCorrectness']
records=read(e/'final/metadata.json')
assert len(records)==316 and records[:313]==read(parent/'final/metadata.json')
assert [r['target_name']for r in records[-3:]]==['AspisV8R19/'+n for n in names]
deps=read(e/'final/dependency-pins.json');assert len(deps)==227
for path,h in deps.items():
    marker='/aspis-r57-lean-src-20260929-a/'
    if marker in path:assert sha(root/'lean'/path.split(marker,1)[1])==h,path
olddeps=read(parent/'final/dependency-pins.json')
for path,h in deps.items():
    if '/aeneas-full/' in path:assert olddeps[path]==h,path
res=read(e/'final/resources.json')
assert {k:res[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']}=={
    'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'}
metrics={};audits=[]
for r,n,count in zip(records[-3:],names,[13,2,10]):
    src=root/'lean'/(r['target_name']+'.lean');s=src.read_text()
    assert r['source_sha256']==sha(src) and r['base_revision']==base and r['exit']==0
    assert r['toolchain']=='leanprover/lean4:v4.32.0'
    assert '-j1' in r['command'] and '-M4500' in r['command']
    assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',s)
    assert 'maxHeartbeats' not in s and 'TraversalRuntime' not in s
    log=(e/'final'/(n+'.log')).read_text()
    assert 'sorryAx' not in log and 'error:' not in log
    got=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
    assert len(got)==count
    for name,axs in got:
        assert {v.strip()for v in axs.split(',')}<={'propext','Classical.choice','Quot.sound'}
        audits.append(name)
    assert re.findall(r'\tExit status: (\d+)',log)==['0']
    assert re.findall(r'\tSwaps: (\d+)',log)==['0']
    wall=re.findall(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[0]
    metrics[n]={'exit':0,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(wall.split(':')))),2),
                'peak_rss_kib':int(re.findall(r'Maximum resident set size \(kbytes\): (\d+)',log)[0])}
receipt={'base_revision':base,'compiled_targets':3,'cached_targets':313,'theorems':audits,
    'metrics':metrics,'new_axioms':0,'generated_canonical_product_proved':True,
    'source_binding':'R69 exact extraction and measured fixed-arity helper; unchanged source bodies',
    'elf_sha256':read(parent/'receipt.json')['elf_sha256'],'cu':[1495663,1497050],
    'runtime_changed':False,'runtime_rerun':False,'actual_1M_gate_passed':False,
    'circle_execution_proved':False,'full_privacy':False,'full_soundness':False,
    'first_remaining':'Transport the retained R66 square/inverse execution to the R69 generated namespace and compose the complete circle map with its actual error order, then the bounded sampler.'}
files=[root/'lean/AspisV8R19'/(n+'.lean')for n in names]
files += [root/'lean/AspisR69Explicit'/(n+'.lean')for n in ['Types','Funs']]
files += [root/'tools'/n for n in ['check_r70_evidence.py','collect_r70_evidence.py','run_r70_lean.py',
    'run_r68_lean.py','run_r64_lean.py','run_r63_lean.py','r69_explicit_product.rs','check_r69_evidence.py']]
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
print(json.dumps({'audit':'PASS','theorems':len(audits),'metrics':metrics,'full_privacy':False,'artifacts':len(manifest)},indent=2))
