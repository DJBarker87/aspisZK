from pathlib import Path
import json,re,hashlib
H=Path('/home/dombarker/project-offloads/codex-cx-stage2b-20261020');rows=[]
for stage in ['stage1_logs','logs']:
 values={}
 for kind in ['candidate','baseline-refreshed']:
  j=json.loads((H/'runs-profile'/kind/'evidence.json').read_text())['execution'];logs=j[stage];previous=1400000;v={}
  for i,l in enumerate(logs):
   if 'r1:' in l and i+1<len(logs) and (m:=re.search(r'consumption: (\d+) units remaining',logs[i+1])):
    now=int(m[1]);v[l]=dict(remaining=now,cost_since_previous_mark=previous-now);previous=now
  values[kind]=v
 for label,v in values['candidate'].items():
  if label in values['baseline-refreshed']:
   b=values['baseline-refreshed'][label];rows.append(dict(stage=stage,phase=label,candidate=v['cost_since_previous_mark'],baseline=b['cost_since_previous_mark'],delta=v['cost_since_previous_mark']-b['cost_since_previous_mark']))
for r in rows:print(r)
(H/'profile-comparison.json').write_text(json.dumps(rows,indent=2)+'\n')
