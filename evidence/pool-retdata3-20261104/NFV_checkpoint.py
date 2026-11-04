from pathlib import Path
import json
E=Path(__file__).resolve().parent
def checkpoint():
 rows=[json.loads(l) for l in (E/'NFV_ATTEMPTS.jsonl').read_text().splitlines()]
 used={k:sum((r['kind'] not in ['kani','extract']) if k=='lean' else r['kind']==k for r in rows) for k in ['kani','lean','extract']}
 limits=dict(kani=80,lean=50,extract=1);remaining={k:limits[k]-used[k] for k in limits}
 assert all(n>=0 for n in remaining.values())
 out=dict(limits=limits,used=used,remaining=remaining)
 (E/'NFV_BUDGET.json').write_text(json.dumps(out,indent=1)+'\n')
 if remaining['kani']<15 or sum(remaining.values())<15:
  for name in ['NFV_HANDOFF.md','NFV_REMAINING.md','NFV_CONE_DELTA.md']:
   p=E/name;s=p.read_text().split('\n<!-- budget checkpoint -->')[0]
   p.write_text(s+'\n<!-- budget checkpoint -->\n'+json.dumps(out,sort_keys=True)+'\n')
  p=E/'NFV_AUDIT.json';audit=json.loads(p.read_text());audit['budget_checkpoint']=out;p.write_text(json.dumps(audit,indent=1)+'\n')
