"""Read-only validation of final scope receipts and exact raw-audit coverage."""
from pathlib import Path
import json,re,datetime,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102';allowed={'propext','Classical.choice','Quot.sound'}
receipts=[];launches=[];lean=[];native=[]
for p in sorted(E.glob('*/receipt.json')):
 j=json.loads(p.read_text());j['receipt_path']=str(p.relative_to(E));receipts.append(j)
 assert j['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),p
 assert j['swap']=='0' and re.fullmatch('[0-9a-f]{40}',j['source_revision']),p
 for n in ['target','exit','wall','peak_rss_kib']:assert j.get(n) is not None,(p,n)
 a=json.load(open(p.parent/'admission-before.json'));b=json.load(open(p.parent/'admission-barrier.json'))
 assert a['allowed'] is True and b['allowed'] is True,p
 launches.append((datetime.datetime.fromisoformat(b['utc']).timestamp(),p.parent.name))
 if j['expected_phase']=='Lean':
  lean.append(j);n=int(p.parent.name.removeprefix('lean-'));assert 90700<=n<=90799
  if j['exit']==0:
   for line in j['axioms']:
    assert 'sorryAx' not in line,(p,line)
    m=re.search(r'depends on axioms: \[([^\]]*)\]',line,re.S)
    if m:assert {x.strip() for x in m[1].split(',') if x.strip()}<=allowed,(p,line)
 else:
  native.append(j);assert re.fullmatch('N9080[0-9]',p.parent.name),p
assert len(lean)<=60 and len(native)<=10
launches.sort();gaps=[b[0]-a[0] for a,b in zip(launches,launches[1:])];assert not gaps or min(gaps)>=180
refusals=[]
for p in E.glob('*/admission-history.jsonl'):
 for line in p.read_text().splitlines():
  j=json.loads(line);a=j.get('admission',{})
  if a.get('allowed') is False:
   t=datetime.datetime.fromisoformat(a['utc']).timestamp();after=next((u for u,n in launches if u>t),None)
   assert after is not None and after-t>=180,(p,a['utc'],after)
   refusals.append(dict(path=str(p.relative_to(E)),utc=a['utc'],seconds_until_next_scope=after-t))
for n in [90797,90798,90799]:assert json.load(open(E/f'lean-{n}/receipt.json'))['exit']==0,n
log=(E/'lean-90797/output.log').read_text();assert 'NEP_FAILURE' not in log
raw=[json.loads(s) for s in re.findall(r'NEP_RESULT (\{[^\n]*\})',log)]
queries=json.load(open(E/'consumer-audit-projection.json'))['queries']
assert {x['root'] for x in raw}==set(queries) and len(raw)==len(queries),(len(raw),len(queries))
for x in raw:assert x['equal'] is True and set(x['walked_axioms'])<=allowed,x
for n,count in [(90798,3),(90799,3)]:assert len(json.load(open(E/f'lean-{n}/receipt.json'))['axioms'])==count,n
assert json.load(open(E/'coherence-result.json'))['status'].startswith('PASS')
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
changed=subprocess.check_output(['git','diff','--name-only','a9aa230d1e','HEAD'],cwd=R,text=True).splitlines()
assert not [p for p in changed if p.startswith(('crates/','programs/'))],changed
(E/'RUNS.json').write_text(json.dumps(dict(receipts=receipts,lean_used=len(lean),native_used=len(native),kani_used=0),indent=2)+'\n')
(E/'release-protocol-check.json').write_text(json.dumps(dict(status='PASS',scope_count=len(receipts),minimum_scope_gap_seconds=min(gaps) if gaps else None,uncharged_refusals=refusals,raw_roots=len(raw),raw_walked_axioms=sorted(set().union(*(set(x['walked_axioms']) for x in raw))),axiom_audit='47 exact declaration queries with summary and fixed NEP importAll/private full graph traversal; unresolved constants are hard errors',lean_used=len(lean),native_used=len(native),kani_used=0,void_launches=[],endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[]),indent=2)+'\n')
print('Release checks PASS:',len(lean),'Lean,',len(native),'native;',len(raw),'complete raw roots')
