#!/usr/bin/env python3
"""Audit premise removal in the owned model, without claiming native closure."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(E/'s1-closed-preparation-targets.json');a=load(E/'accepted-targets.json')['targets'];pins=load(E/'s1-closed-preparation-import-pins.json');total=0.;peak=0;reports=0
for target,attempt in m['targets'].items():
 r=load(E/attempt/'receipt.json');p=S/(target+'.lean');s=p.read_text()
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms']
 assert a[target]['receipt']==attempt+'/receipt.json'
 assert sha(p)==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][target]['source_sha256']
 assert r['object_sha256']==pins['targets'][target]['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',s,re.M)
 for report in r['print_axioms']:
  if 'does not depend on any axioms' not in report:
   x=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S)
   assert x and set(re.findall(r'[A-Za-z_.]+',x[1]))<={'propext','Classical.choice','Quot.sound'}
  reports+=1
 total+=r['wall_seconds'];peak=max(peak,r['peak_rss_bytes'])
s=(S/'S1CurrentOwnedClosedJoinV1.lean').read_text()
assert '(sampling :' not in s and '(embed :' not in s and '(hfirst :' not in s
assert 'AdapterRw.r1_pool_adapter.owned.stage1_owned' in s and 'ExactSerializedRankTrace' in s
assert 'afterPrepare (closedInstall ops)' in s
assert m['sampling_seed_irrelevant'] and not any(m[k] for k in ['native_claim_refinement','native_sdk_state_binding','whole_s1_closed'])
for path,expected in load(E/'s1-closed-preparation-tool-pins.json')['scripts'].items():assert sha(R/path)==expected
for name,expected in load(E/'s1-closed-preparation-reused-pins.json')['packets'].items():assert sha(E/name)==expected
print(json.dumps(dict(targets=len(m['targets']),wall_seconds=total,peak_rss_bytes=peak,swaps=0,standard_or_empty_axiom_reports=reports,sampling_seed_irrelevant=True,whole_s1_closed=False)))
