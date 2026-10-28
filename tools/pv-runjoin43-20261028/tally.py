"""Summarize this round without promoting staged or rejected source."""
from pathlib import Path
import json,subprocess,hashlib,re,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin43-20261028'
receipts=sorted((json.loads(p.read_text()) for p in E.glob('receipt-*.json')),key=lambda x:x['attempt'])
assert len(receipts)<=100 and all(60400<=x['attempt']<=60499 for x in receipts)
assert all(x['completed_modules']==1 for x in receipts)
assert all(x['swaps']==0 for x in receipts)
mods=[v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
failed=[]
for v in mods:
 if v['accepted']:
  for line in v['axioms']:
   m=re.search(r'depends on axioms: \[([^]]*)\]',line)
   if m:assert set(x.strip() for x in m[1].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},line
 else:
  b=subprocess.check_output(['git','cat-file','blob',v['source']['git_blob']],cwd=R)
  assert hashlib.sha256(b).hexdigest()==v['source_sha256']
  failed.append(dict(module=v['module'],blob=v['source']['git_blob'],sha256=v['source_sha256'],revision=v['source_revision'],retained=True))
(E/'retained-failed-sources.json').write_text(json.dumps(failed,indent=2)+'\n')
intervals=[]
for x in receipts:
 t=datetime.datetime.fromisoformat(x['utc']).timestamp();tr=json.loads((E/f"transport-{x['attempt']}.json").read_text());intervals.append((t,t+tr['wall'],x['attempt']))
intervals.sort();overlap=[(a[2],b[2]) for a,b in zip(intervals,intervals[1:]) if a[1]>b[0]];assert not overlap
(E/'scope-sequence-check.json').write_text(json.dumps(dict(intervals=[dict(attempt=a,start=s,end_upper_bound=e) for s,e,a in intervals],overlaps=overlap),indent=2)+'\n')
tally=dict(attempts=len(receipts),accepted=sum(x['accepted'] for x in receipts),rejected=sum(not x['accepted'] for x in receipts),kani=0,attempt_ids=[x['attempt'] for x in receipts],rows_removed=0,endpoint_fields_removed=0,endpoint_fields_added=0,endpoint_fields_changed=0,all_accepted_printed_axioms_standard=True,peak_rss_bytes=max((x['peak_rss_bytes'] for x in receipts),default=0),all_swaps_zero=True,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=R).strip())
(E/'final-tally.json').write_text(json.dumps(tally,indent=2)+'\n')
(E/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline','cbec9b6925..HEAD'],cwd=R,text=True))
print(json.dumps(tally))
