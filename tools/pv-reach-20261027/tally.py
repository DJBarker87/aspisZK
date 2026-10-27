"""Account charged compiler invocations separately from allocated/refused IDs."""
from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027'
rows=sorted((json.loads(p.read_text()) for p in E.glob('receipt-[0-9]*.json')),key=lambda x:x['attempt'])
used=sorted(int(p.stem[5:]) for p in E.glob('used-*.json'))
assert len(rows)<=100 and len(used)==len(set(used))
assert all(44000<=i<=44499 for i in used)
assert not set(used)&set(range(44200,44500))
assert all(r.get('reservation',{}).get('allowed') for r in rows)
for r in rows:
 for report in r['axioms']:
  if r['accepted'] and 'depends on axioms:' in report:
   a={x.strip() for x in report.split('depends on axioms: [')[1].split(']')[0].split(',')}
   assert a<={'propext','Classical.choice','Quot.sound'},report
 for line in (E/f'time-{r["attempt"]}.log').read_text().splitlines():
  if 'Elapsed (wall clock)' in line:r['time_wall']=line.split('):',1)[1].strip()
 # Early source edits were retained in exact snapshots; do not imply all
 # snapshot bytes were already committed at the recorded parent revision.
 snapshot=E/r['source_snapshot']
 origin='docs/research/v8-r0-zk-20261009/lean/'+r['target']+'.lean'
 blob=subprocess.run(['git','show',r['source_revision']+':'+origin],capture_output=True).stdout
 r['source_bytes_at_recorded_revision']=(blob==snapshot.read_bytes())
 r['peak_rss_kib']=r['peak_rss_bytes']//1024 if r['peak_rss_bytes'] is not None else None
x=dict(budget=100,charged=len(rows),green=sum(r['accepted'] for r in rows),failed=sum(not r['accepted'] for r in rows),allocated_ids=used,zero_compile_ids=sorted(set(used)-{r['attempt'] for r in rows}),kani=0,audit_reserve=3,remaining=100-len(rows),shared_sources_written=False,receipts=rows)
(E/'receipt-index.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:v for k,v in x.items() if k!='receipts'}))
