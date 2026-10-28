"""Audit owned receipts and source pins; no build or compiler invocation."""
from pathlib import Path
import json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin32-20261028'
receipts=sorted((json.loads(p.read_text()) for p in E.glob('receipt-*.json')),key=lambda r:r['attempt']);records=[(int(p.stem.split('-')[1]),v) for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
accepted={};fail=[];bad_axioms=[]
for a,v in records:
 if v['accepted']:
  assert v['module'] not in accepted,('accepted module repeated',a,v['module'])
  accepted[v['module']]=dict(attempt=a,**v)
  for ax in v['axioms']:
   if 'depends on axioms: [' in ax:
    names={n.strip() for n in ax.split('depends on axioms: [',1)[1].split(']',1)[0].replace('\n','').split(',')}
    if names-{'propext','Classical.choice','Quot.sound'}:bad_axioms.append(dict(module=v['module'],attempt=a,axioms=ax))
 else:fail.append(dict(module=v['module'],attempt=a,exit=v['exit']))
assert not bad_axioms,bad_axioms
assert len(receipts)<=100
assert all(51300<=r['attempt']<=51499 for r in receipts)
assert all(r['swaps']==0 for r in receipts)
pending=[]
for p in E.glob('transport-[0-9]*.json'):
 a=int(p.stem.split('-')[1]);v=json.loads(p.read_text())
 if a not in {r['attempt'] for r in receipts} and v.get('exit')==0:pending.append(a)
result=dict(charged=len(receipts)+len(pending),remaining=100-len(receipts)-len(pending),completed_receipts=len(receipts),confirmed_completed_pending_collection=sorted(pending),accepted_attempts=sum(r['accepted'] for r in receipts),rejected_attempts=sum(not r['accepted'] for r in receipts),accepted_modules=len(accepted),failed_modules=fail,kani=0,axiom_reports=sum(len(v['axioms']) for v in accepted.values()),nonstandard_axioms=bad_axioms,peak_rss_bytes=max([r['peak_rss_bytes'] or 0 for r in receipts]+[0]),nonzero_swaps=[],used_ids=[r['attempt'] for r in receipts])
(E/'tally.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'receipt-index.tsv').write_text('attempt\tmodules\texit\thost_wall_s\tpeak_rss_bytes\tswap\taccepted\n'+''.join(f"{r['attempt']}\t{r['completed_modules']}\t{r['exit']}\t{r['host_wall_seconds']}\t{r['peak_rss_bytes']}\t{r['swaps']}\t{r['accepted']}\n" for r in receipts))
(E/'accepted-object-index.json').write_text(json.dumps({m:{k:v[k] for k in ['attempt','source_sha256','object_sha256','deps_fingerprint']} for m,v in accepted.items()},indent=2)+'\n')
print(json.dumps(result))
