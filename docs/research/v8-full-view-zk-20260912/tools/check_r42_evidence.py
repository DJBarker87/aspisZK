#!/usr/bin/env python3
"""Offline gate: finite conditional bound is NOT a completed source privacy theorem."""
import hashlib,json,re
from fractions import Fraction
from math import prod
from pathlib import Path
root=Path(__file__).resolve().parent.parent;e=root/'evidence/r42-admissible-grid'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((e/'MANIFEST.json').read_text())
for n,h in manifest.items():assert sha(e/n)==h,n
r=json.loads((e/'receipt.json').read_text());assert r['new_lean_declarations']==6 and r['root_count']==262144
assert not any(r[k] for k in ['source_distribution_bound','full_privacy','verifier_changed','new_sbf_measurement'])
old=json.loads((e/'control/r18-stage.json').read_text());new=json.loads((e/'query/r18-stage.json').read_text());mid=json.loads((e/'roots/r18-stage.json').read_text())
assert len(old['files'])==195 and len(mid['files'])==196 and len(new['files'])==197
assert sha(e/'control/r18-stage.json')==sha(root/'evidence/r41-qm31-residual/r18-stage.json')
cargo='docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'
for n,h in old['files'].items():
    if n!=cargo:assert mid['files'][n]==new['files'][n]==h,n
for n,h in r['inspected_source_sha256'].items():
    assert sha(e/'source'/n)==h,n
    if n in new['files']:assert new['files'][n]==h,n
for name in ['root_support','query_control']:
    key='docs/research/v8-no-work-100-20260907/experiments/r42_'+name+'.rs'
    assert new['files'][key]==sha(root/'tools'/('r42_'+name+'.rs'))
records=json.loads((e/'lean-b/metadata.json').read_text());assert len(records)==178
for record in records:assert record['exit']==0 and record['source_sha256']==sha(root/'lean'/(record['target_name']+'.lean')) and record['toolchain']=='leanprover/lean4:v4.32.0'
def metrics(log):
    assert '\tExit status: 0'in log and '\tSwaps: 0'in log
    rss=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1))
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log).group(1).split(':')
    return sum(float(x)*60**i for i,x in enumerate(reversed(t))),rss
lean=[]
for name in ['AdmissibleGridBound','QM31AdmissibleGrid']:
    log=(e/f'lean-b/{name}.log').read_text();assert 'sorryAx'not in log and log.count('depends on axioms:')==3
    for ax in re.findall(r'depends on axioms: \[([^]]*)\]',log):assert set(ax.replace('\n',' ').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
    lean.append(metrics(log));s=(root/f'lean/AspisV8R19/{name}.lean').read_text()
    for bad in ['native_decide','sorry','axiom ','maxRecDepth','norm_num']:assert bad not in s
failed=(e/'lean-a/AdmissibleGridBound.log').read_text();assert 'Type mismatch'in failed and '\tExit status: 1'in failed
rust=[]
for folder,target in [('roots','root-support'),('query','query-control')]:
    meta=json.loads((e/folder/'metadata.json').read_text());assert meta['overflow_checks'] and not meta['sampler_law'] and not meta['full_privacy']
    assert meta['source_manifest_sha256']==sha(e/folder/'r18-stage.json')
    assert '--release'in meta['commands'][0]['command'] and '--offline'in meta['commands'][0]['command'] and '--locked'in meta['commands'][0]['command']
    assert all(c['exit']==0 for c in meta['commands'])
    for name in ['compile',target]:rust.append(metrics((e/folder/(name+'.log')).read_text()))
rootlog=(e/'roots/root-support.log').read_text();assert 'roots=262144 source_points=262144 integer_reference_checks=262144 unique=262144'in rootlog
assert 'wrong_order_negative=261632 duplicate_negative=1 out_of_range_negative=2'in rootlog
assert 'ordered_root_sha256=e417c33d590558595f5a27abc44cfe9fc6985b02bce7d17fcc974025033ba4a1'in rootlog
assert 'first_hit_cases=43 failure_cases=21 early_return_cases=5 extra_detection_blocks=5 next_block_checks=43'in (e/'query/query-control.log').read_text()
n=262144;distinct=Fraction(prod(n-i for i in range(22)),n**22);bound=Fraction(1105,n)/distinct
assert Fraction(*r['ideal_query_distinct_fraction'])==distinct and Fraction(*r['ideal_query_only_conditioned_bound'])==bound
assert Fraction(4,1000)<bound<Fraction(5,1000)
print(json.dumps({'status':'PASS','artifacts':len(manifest),'lean_theorems':6,'lean_wall_seconds':round(sum(t for t,_ in lean),2),'lean_peak_rss_kib':max(rss for _,rss in lean),'rust_wall_seconds':round(sum(t for t,_ in rust),2),'rust_peak_rss_kib':max(rss for _,rss in rust),'source_root_support':n,'source_control_cases':69,'source_distribution_bound':False,'full_privacy':False,'new_sbf_measurement':False},indent=2))
