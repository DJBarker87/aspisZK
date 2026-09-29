#!/usr/bin/env python3
"""Offline point-weight gate: model linkage, kernel audits, source pins, failures."""
import hashlib,json,re
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r39-point-weight-certificate';prior=root/'evidence/r38-root-certificate'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
receipt=json.loads((e/'receipt.json').read_text());assert receipt['source_pins']==194 and receipt['new_lean_declarations']==782
assert not any(receipt[k]for k in['full_privacy','nonzero_kernel_certificate','verifier_changed'])
m=json.loads((e/'r18-stage.json').read_text());old=json.loads((prior/'r18-stage.json').read_text());ex='docs/research/v8-no-work-100-20260907/experiments/'
assert receipt['source_manifest_sha256']==sha(e/'r18-stage.json')and len(m['files'])==194
assert m['r39_generator']['control_manifest_sha256']==sha(prior/'r18-stage.json')
for n,h in old['files'].items():
    if n!=ex+'performance-host/Cargo.toml':assert m['files'][n]==h,n
for n,h in m['files'].items():
    if(e/'source'/n).exists():assert sha(e/'source'/n)==h,n
assert sha(root/'tools/r39_point_generator.rs')==m['files'][ex+'r39_point_generator.rs']
runtime=json.loads((e/'runtime/metadata.json').read_text());assert runtime['source_manifest_sha256']==sha(e/'r18-stage.json')and runtime['overflow_checks']and len(runtime['generated'])==70
for n,h in runtime['generated'].items():assert sha(root/'lean/AspisV8R19'/n)==h,n
for label in['compile','write','check']:
    log=(e/f'runtime/{label}.log').read_text();assert '\tExit status: 0'in log and '\tSwaps: 0'in log
    if label!='compile':
        for s in['point_checks=30','tensor_checks=3072','code_checks=333','weight_checks=324','table_checks=2048']:assert s in log
        assert int(re.search(r'pivot_negative_entries=(\d+)',log).group(1))>0
records=json.loads((e/'lean-e/metadata.json').read_text());assert len(records)==124
for r in records:assert r['exit']==0 and r['source_sha256']==sha(root/'lean'/(r['target_name']+'.lean'))and r['toolchain']=='leanprover/lean4:v4.32.0'
checks=[('c','PointWeightCertificate',2),('d','WitnessPointData',0),('d','WitnessPoints',3),('d','WitnessPointPreflight',3),('e','WitnessPointBridge',9)]
checks += [('e',f'WitnessChordSupport{i:02}',12)for i in range(9)]
for i in range(3):
    checks += [('e',f'WitnessCode{i}Chunk{j:02}',min(12,111-12*j))for j in range(10)]
    checks += [('e',f'WitnessWeight{i}Chunk{j:02}',12)for j in range(9)]
assert sum(n for _,_,n in checks)==782
max_rss=0;wall_sum=0
for folder,name,count in checks:
    log=(e/f'lean-{folder}/{name}.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==count and '\tExit status: 0'in log and '\tSwaps: 0'in log,name
    for ax in re.findall(r'depends on axioms: \[([^]]*)\]',log):assert set(ax.replace('\n',' ').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
    max_rss=max(max_rss,int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1)))
    time=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':');wall_sum+=sum(float(x)*60**i for i,x in enumerate(reversed(time)))
failed=(e/'lean-b/WitnessPointPreflight.log').read_text();assert 'maximum recursion depth'in failed and '\tExit status: 1'in failed
for n in runtime['generated']:
    s=(root/'lean/AspisV8R19'/n).read_text()
    for bad in['native_decide','norm_num','sorry','maxRecDepth','rootRun']:assert bad not in s,(n,bad)
    if n.startswith('WitnessWeight'):assert s.count('PointWeightCertificate.sparse_sum')==12
bridge=(root/'lean/AspisV8R19/WitnessPointBridge.lean').read_text();assert bridge.count('PointWeightCertificate.point_weight_stages')==3
print(json.dumps({'status':'PASS','artifacts':len(manifest),'new_lean_declarations':782,'point_code_weight_coordinates':687,'chord_support_rows':108,'lean_wall_seconds_sum':round(wall_sum,2),'lean_peak_rss_kib':max_rss,'point_weight_model_bridge':True,'dense_preflight_failure_retained':True,'nonzero_kernel_certificate':False,'full_privacy':False},indent=2))
