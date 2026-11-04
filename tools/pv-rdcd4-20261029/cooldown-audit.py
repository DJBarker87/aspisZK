"""Audit actual launch barriers and refusal-to-launch intervals, locally."""
from pathlib import Path
from datetime import datetime
import json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
def stamp(x):return datetime.fromisoformat(x).timestamp()
launches=[];refusals=[]
for p in E.glob('*/receipt.json'):
 b=json.load(open(p.parent/'admission-barrier.json'));a=json.load(open(p.parent/'admission-before.json'))
 assert b['allowed'] is True and a['allowed'] is True,p
 launches.append((stamp(b['utc']),str(p.parent.name),b['utc']))
for p in list(E.glob('*/admission-history.jsonl'))+list(E.glob('*/barrier-history.jsonl')):
 for line in p.read_text().splitlines():
  x=json.loads(line);a=x.get('admission',{})
  if a.get('allowed') is False and a.get('utc'):refusals.append((stamp(a['utc']),str(p),a['utc']))
launches.sort();gaps=[dict(previous=a[1],next=b[1],seconds=b[0]-a[0]) for a,b in zip(launches,launches[1:])]
violations=[x for x in gaps if x['seconds']<180]
refusal_gaps=[]
for r in refusals:
 after=next((x for x in launches if x[0]>r[0]),None)
 if after:
  x=dict(refusal=r[1],launch=after[1],seconds=after[0]-r[0]);refusal_gaps.append(x)
  if x['seconds']<180:violations.append(x)
assert not violations,violations
out=dict(actual_launches=len(launches),minimum_launch_gap_seconds=min(x['seconds'] for x in gaps),violations=violations,launch_gaps=gaps,refusal_to_launch=refusal_gaps,qualification='Actual barrier UTCs; local waits do not count as submissions. No admission/refusal record is removed.')
(E/'cooldown-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(out['actual_launches'],'actual launches; min gap',out['minimum_launch_gap_seconds'],'seconds; zero violations')
