from pathlib import Path
import json,subprocess,re,hashlib,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownd-20261029'
rows=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
assert all(63200<=r['attempt']<=63299 for r in rows)
assert len({r['attempt'] for r in rows})==len(rows)
refusals=[];launches=[]
for p in E.glob('**/admission-*.json'):
 try:j=json.loads(p.read_text())
 except json.JSONDecodeError:continue
 if j.get('allowed') is False:refusals.append((datetime.datetime.fromisoformat(j['utc']).timestamp(),str(p)))
 if p.name=='admission-launch.json' and j.get('allowed') is True:
  receipt=p.parent/'receipt.json'
  if receipt.exists():launches.append((datetime.datetime.fromisoformat(j['utc']).timestamp(),str(p)))
cool=[]
for t,p in refusals:
 future=[(s,q) for s,q in launches if s>t]
 if future:
  s,q=min(future);cool.append(dict(refusal=p,next_launch=q,seconds=s-t));assert s-t>=180,(p,q,s-t)
for r in rows:
 a=json.loads((E/f"lean-{r['attempt']}/admission-launch.json").read_text());b=json.loads((E/f"lean-{r['attempt']}/admission-barrier.json").read_text())
 assert a['allowed'] is True and b['allowed'] is True
 if r['exit']==0:assert 'sorryAx' not in r['print_axioms']
native=[json.loads(p.read_text()) for p in E.glob('native-*/receipt.json')]
summary=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),lean_starts=len(rows),lean_pass=sum(r['exit']==0 for r in rows),lean_fail=sum(r['exit']!=0 for r in rows),native_scopes=len(native),kani=0,max_lean_rss_kib=max(int(r['peak_rss_kib']) for r in rows),all_swaps_zero=all(int(r['swap'])==0 for r in rows+native),cooldowns=cool,rows=rows,native=native)
(E/'combined-audit.json').write_text(json.dumps(summary,indent=2)+'\n');print({k:v for k,v in summary.items() if k not in ['rows','native','cooldowns']});print('cooldown minimum',min((r['seconds'] for r in cool),default=None))
