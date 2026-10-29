"""Read-only evidence audit; charged launches only, no reruns or host mutation."""
from pathlib import Path
from datetime import datetime
import json
E=Path(__file__).resolve().parents[2]/'evidence/pv-rdcd3-20261028'
events=[]
for p in E.glob('*/admission-history.jsonl'):
 for line in p.read_text().splitlines():
  x=json.loads(line);a=x['admission']
  if a.get('allowed') is False and a.get('utc'):events.append((datetime.fromisoformat(a['utc']).timestamp(),'refusal',p.parent.name))
for p in E.glob('*/barrier-history.jsonl'):
 for line in p.read_text().splitlines():
  x=json.loads(line);a=x['admission']
  if a.get('utc') and (a.get('allowed') is False or (p.parent/'receipt.json').exists()):
   events.append((datetime.fromisoformat(a['utc']).timestamp(),'launch' if a.get('allowed') is True else 'refusal',p.parent.name))
events=sorted(set(events));previous=None;violations=[];gaps=[]
for stamp,kind,target in events:
 if kind=='launch' and previous:
  gap=stamp-previous[0];gaps.append(dict(target=target,previous=previous[2],seconds=gap))
  if gap<180:violations.append(gaps[-1])
 previous=(stamp,kind,target)
j=dict(launches=sum(k=='launch' for _,k,_ in events),refusals=sum(k=='refusal' for _,k,_ in events),minimum_gap_seconds=min((x['seconds'] for x in gaps),default=None),violations=violations,qualification='Host admission/barrier utc evidence, comparing every credited launch with the preceding actual launch or refusal. Local pre-submission cooldown refusals launch nothing and are not compiler attempts. Historical pv-rdcd violations remain separately recorded; no credit imported from void objects.')
(E/'cooldown-audit.json').write_text(json.dumps(j,indent=2)+'\n');print(j);assert not violations
