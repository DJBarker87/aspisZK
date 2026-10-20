"""Pick actual accepted inputs exercising new-format extremes; never alter FS queries.
Includes both batch node extrema, sort-inversion extrema and every folded duplicate.
Usage: pick_adopted_targets.py host-root set...
"""
import sys,json,collections
from pathlib import Path
H=Path(sys.argv[1]);rows=[]
for sset in sys.argv[2:]:
 p=H/'sweep'/sset/'sweep.jsonl'
 if not p.exists():continue
 for line in p.read_text().splitlines():
  row=json.loads(line)
  if row.get('outcome')!='accepted':continue
  for line in (p.parent/'runs'/row['label']/'stderr.log').read_text().splitlines():
   if not line.startswith('FORMAT_ADOPT_NATIVE='):continue
   d=json.loads(line.split('=',1)[1]);q=d['queries'];a=q[:10];b=q[10:];row.update(sset=sset,native=d)
   row['metrics']=[sum(d['slot_nodes'][:3]),sum(d['slot_nodes'][3:])]
   row['metrics'] += [sum(v[i]>v[j] for i in range(len(v)) for j in range(i+1,len(v))) for v in [a,b]]
   row['duplicates']=[len(set(u//4 for u in v))<len(v) for v in [a,b]]
   rows.append(row)
by=collections.defaultdict(list)
for r in rows:by[r['kind']].append(r)
picks={}
for k,rs in by.items():
 for m in range(4):
  for f in (min,max):
   r=f(rs,key=lambda r:r['metrics'][m]);picks[(r['sset'],r['label'])]=r
 for r in rs:
  if any(r['duplicates']):picks[(r['sset'],r['label'])]=r
print(' '.join(f'{s}:{l}' for s,l in picks))
(H/'target-selection.json').write_text(json.dumps([{'set':s,'label':l,'metrics':r['metrics'],'folded_duplicates':r['duplicates'],'queries':r['native']['queries'],'slot_nodes':r['native']['slot_nodes']} for (s,l),r in picks.items()],indent=1))
