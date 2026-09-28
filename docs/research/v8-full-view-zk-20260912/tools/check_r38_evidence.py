#!/usr/bin/env python3
"""Offline root-certificate gate; full determinant evaluation remains separate."""
import hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r38-root-certificate';prior=root/'evidence/r37-source-restricted-residual'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
r=json.loads((e/'receipt.json').read_text());assert r['source_pins']==193 and r['new_lean_declarations']==39
assert not any(r[k]for k in['full_privacy','nonzero_kernel_certificate','verifier_changed'])
m=json.loads((e/'r18-stage.json').read_text());old=json.loads((prior/'r18-stage.json').read_text());ex='docs/research/v8-no-work-100-20260907/experiments/'
assert r['source_manifest_sha256']==sha(e/'r18-stage.json')and len(m['files'])==193
assert m['r38_generator']['control_manifest_sha256']==sha(prior/'r18-stage.json')
for n,h in old['files'].items():
    if n!=ex+'performance-host/Cargo.toml':assert m['files'][n]==h,n
for n,h in m['files'].items():
    if(e/'source'/n).exists():assert sha(e/'source'/n)==h,n
assert sha(root/'tools/r38_root_generator.rs')==m['files'][ex+'r38_root_generator.rs']
runtime=json.loads((e/'runtime/metadata.json').read_text());assert runtime['source_manifest_sha256']==sha(e/'r18-stage.json')and runtime['overflow_checks']and len(runtime['generated'])==28
for n,h in runtime['generated'].items():assert sha(root/'lean/AspisV8R19'/n)==h,n
for label in['compile','write','check']:
    log=(e/f'runtime/{label}.log').read_text();assert '\tExit status: 0'in log and '\tSwaps: 0'in log
    if label!='compile':assert 'source_coordinate_checks=702'in log and 'zero_extension_checks=26'in log
records=json.loads((e/'lean-c/metadata.json').read_text());assert len(records)==53
for r in records:assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))and r['toolchain']=='leanprover/lean4:v4.32.0'
checks=[('a','RootCertificate',4),('b','WitnessRootData',0),('b','WitnessRootStep01',1),('b','WitnessRootStep22',1),('c','WitnessRootBridge',9)]
checks += [('c',f'WitnessRootStep{i:02}',1)for i in range(2,22)]+[('c',f'WitnessShiftStep{i}',1)for i in range(1,5)]
assert sum(n for _,_,n in checks)==39
max_rss=0;wall_sum=0
for folder,name,count in checks:
    log=(e/f'lean-{folder}/{name}.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count and '\tExit status: 0'in log and '\tSwaps: 0'in log
    max_rss=max(max_rss,int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1)))
    time=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':');wall_sum+=sum(float(x)*60**i for i,x in enumerate(reversed(time)))
for n in runtime['generated']:
    s=(root/'lean/AspisV8R19'/n).read_text();assert 'native_decide'not in s and 'norm_num'not in s and 'sorry'not in s
bridge=(root/'lean/AspisV8R19/WitnessRootBridge.lean').read_text();assert bridge.count('apply root_step')==22 and 'rw [initial_vector,root_chain]'in bridge
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_declarations':39,'coordinate_checks':702,'lean_wall_seconds_sum':round(wall_sum,2),'lean_peak_rss_kib':max_rss,'root_model_bridge':True,'nonzero_kernel_certificate':False,'full_privacy':False},indent=2))
