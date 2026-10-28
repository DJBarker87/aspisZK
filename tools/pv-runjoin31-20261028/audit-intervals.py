"""Validate chronological admission evidence; does not submit or monitor jobs."""
from pathlib import Path
import json,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin31-20261028';events={}
def add(row,path):
 if not isinstance(row,dict):return
 if 'admission' in row:add(row['admission'],path)
 if 'utc' not in row or 'allowed' not in row:return
 stamp=datetime.datetime.fromisoformat(row['utc']);key=row['utc']+' '+str(row['allowed'])
 events.setdefault(key,dict(utc=row['utc'],allowed=row['allowed'],error=row.get('error'),reason=row.get('reason'),paths=[]))['paths'].append(path.name)
for p in E.glob('*reservation*.log'):
 for line in p.read_text().splitlines():
  try:add(json.loads(line),p)
  except ValueError:pass
for p in list(E.glob('*refusal*.json'))+list(E.glob('barrier-race-*.json')):
 add(json.loads(p.read_text()),p)
ordered=sorted(events.values(),key=lambda r:r['utc']);intervals=[]
for first,next_event in zip(ordered,ordered[1:]):
 if first['allowed']:continue
 seconds=(datetime.datetime.fromisoformat(next_event['utc'])-datetime.datetime.fromisoformat(first['utc'])).total_seconds()
 assert seconds>=180,(first,next_event,seconds)
 intervals.append(dict(refusal=first['utc'],next_admission=next_event['utc'],seconds=seconds,scan_race=bool(first.get('error')),match=True))
(E/'admission-intervals.json').write_text(json.dumps(dict(events=ordered,refusal_intervals=intervals,all_full_cooldowns=True),indent=2)+'\n')
print('Validated',len(intervals),'full cooldown intervals; pending final refusal has no next admission yet')
