"""Validate completed release receipts, admitted launches, cooldowns and axioms."""
from pathlib import Path
import json,re,datetime,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101';runs=json.load(open(E/'RUNS.json'));receipts=runs['receipts'];launches=[];axioms=set();refusals=[]
for j in receipts:
 p=E/j['receipt_path'];d=p.parent
 assert all(j.get(k) is not None for k in ['target','exit','wall','peak_rss_kib','swap','source_revision']),str(p)
 assert j['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),str(p)
 assert j['swap']=='0' and re.fullmatch('[0-9a-f]{40}',j['source_revision']),str(p)
 a=json.load(open(d/'admission-before.json'));b=json.load(open(d/'admission-barrier.json'));assert a['allowed'] is True and b['allowed'] is True,str(p)
 history=[json.loads(x) for x in (d/'admission-history.jsonl').read_text().splitlines()];last=history[-1];assert last['exit']==0 and last['admission']['allowed'] is True
 launches.append((datetime.datetime.fromisoformat(b['utc']).timestamp(),d.name))
 if j['expected_phase']=='Lean' and j['exit']==0:
  for line in j['axioms']:
   assert 'sorryAx' not in line,line
   match=re.search(r'depends on axioms: \[([^\]]*)\]',line,re.S)
   if match:axioms.update(x.strip() for x in match[1].split(',') if x.strip())
 if j['expected_phase']=='Lean' and j['exit']!=0:
  assert hashlib.sha256((R/j['source_path']).read_bytes()).hexdigest()!=j['source_sha256'],'unchanged failed proof'
assert axioms<={'propext','Classical.choice','Quot.sound'},axioms
launches.sort();gaps=[b[0]-a[0] for a,b in zip(launches,launches[1:])];assert min(gaps)>=180,min(gaps)
for p in E.glob('*/admission-history.jsonl'):
 for line in p.read_text().splitlines():
  x=json.loads(line);a=x['admission']
  if a.get('allowed') is False:
   epoch=datetime.datetime.fromisoformat(a['utc']).timestamp();following=next((t for t,n in launches if t>epoch),None)
   assert following and following-epoch>=180,(str(p),following,epoch)
   refusals.append(dict(target=p.parent.name,utc=a['utc'],exit=x['exit'],error=a.get('error'),bounded_reserved_bytes=a.get('bounded_reserved_bytes'),projected_reserved_bytes=a.get('projected_reserved_bytes'),seconds_until_next_scope=following-epoch))
for n,count in [(78297,123),(78298,3),(78299,3)]:
 j=json.load(open(E/f'lean-{n}/receipt.json'));assert j['exit']==0 and len(j['axioms'])==count,(n,len(j['axioms']))
ids={j['attempt'] for j in receipts if j['expected_phase']=='Lean'};assert ids==set(range(78200,78241))|{78297,78298,78299}
failed={j['attempt'] for j in receipts if j['expected_phase']=='Lean' and j['exit']};assert failed=={78206,78207,78233,78237}
rows=json.load(open(E/'ROWS.json'));assert rows['V197']['status']=='FINDING' and all(rows[n]['status']=='RESTORED' for n in ['V233','V236'])
(E/'release-protocol-check.json').write_text(json.dumps(dict(status='PASS',launches=len(launches),minimum_scope_start_gap_seconds=min(gaps),refusals=refusals,void_launches=[],accepted_axioms=sorted(axioms),audit_query_counts={'78297':123,'78298':3,'78299':3},actual_ids=sorted(ids),uncredited_failed_ids=sorted(failed),limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),scope='read-only local receipt reconciliation; no compiler or regression rerun'),indent=2)+'\n')
print('Release protocol PASS:',len(launches),'scopes; min gap',min(gaps),';',len(refusals),'uncharged refusals; standard axioms only')
