#!/usr/bin/env python3
"""Source-only receipt/body audit. No compiler/solver replay or native closure claim."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021'
S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
P=E/'s1-query-block-extraction-v1';collection=json.loads((P/'collection.json').read_text())
for p,h in collection['files'].items():assert sha(P/p)==h
source=(P/'v3/src/lib.rs').read_text()
assert source==(T/'proofs.rs').read_text().split('#[cfg(kani)]mod proofs{')[0].replace('fn owned_block(', 'pub fn owned_block(')
for n in [1,2,3]:
 for phase in ['charon','aeneas']:
  a=P/f'v{n}/run-extract';r=json.loads((a/(phase+'-receipt.json')).read_text());i=json.loads((a/(phase+'-input.json')).read_text())
  assert r['exit_status']==(2 if phase=='aeneas'and n<3 else 0)
  assert r['swaps']==0 and r['source_unchanged']and r['tools_unchanged']
  assert r['cgroup']['memory.max']==str(2*2**30)and r['cgroup']['memory.swap.max']=='0'
  assert sha(P/f'v{n}/src/lib.rs')==i['source_pins']['src/lib.rs']
for row in json.loads((T/'lean-binding.json').read_text()):
 src=P/f'v3/generated/AspisS1OwnedQueryBlock/{row["original"]}.lean'
 dst=S/(row['checked']+'.lean')
 assert sha(src)==row['original_sha256']and sha(dst)==row['checked_sha256']
 transformed=re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth) .*\n','',src.read_text(),flags=re.M).replace('import AspisS1OwnedQueryBlock.Types','import S1OwnedQueryBlockTypesV1')
 actual=dst.read_text();assert actual.startswith(transformed)
 assert all(not line.strip()or line.startswith('#print axioms ')for line in actual[len(transformed):].splitlines())
metrics=[]
for module,attempt in [('S1OwnedQueryBlockTypesV1','s1-owned-query-block-types-v1'),('S1OwnedQueryBlockFunsV1','s1-owned-query-block-funs-v1'),('S1OwnedQueryContainsTotalV1','s1-owned-query-contains-total-v3'),('S1OwnedQueryStepTotalV1','s1-owned-query-step-total-v1'),('S1OwnedQueryContainsMeaningV1','s1-owned-query-contains-meaning-v2'),('S1OwnedQueryContainsStdV1','s1-owned-query-contains-std-v1'),('S1OwnedQueryBlockTotalV1','s1-owned-query-block-total-v1'),('S1OwnedQueryWordStdV1','s1-owned-query-word-std-v2')]:
 a=E/attempt;r=json.loads((a/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert sha(S/(module+'.lean'))==r['source_sha256']==sha(a/'source.lean')
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',(S/(module+'.lean')).read_text())
 assert 'sorryAx'not in ''.join(r['print_axioms'])
 if module!='S1OwnedQueryBlockTypesV1':assert r['print_axioms']
 metrics.append({k:r[k]for k in ['target','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']})
print(json.dumps(dict(status='PASS',extraction_pins=len(collection['files']),reference_TOTAL_on_bounded_states=True,native_correspondence_not_claimed=True,enclosing_S1_S6_open=True,metrics=metrics)))
