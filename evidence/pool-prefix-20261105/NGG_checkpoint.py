from pathlib import Path
import json
E=Path(__file__).resolve().parent
def checkpoint():
 rows=[json.loads(l) for l in (E/'NGG_ATTEMPTS.jsonl').read_text().splitlines()]
 used={k:sum((r['kind'] not in ['kani','extract']) if k=='lean' else r['kind']==k for r in rows) for k in ['kani','lean','extract']}
 limits=dict(kani=120,lean=60,extract=2);remaining={k:limits[k]-used[k] for k in limits}
 assert all(n>=0 for n in remaining.values())
 out=dict(limits=limits,used=used,remaining=remaining)
 (E/'NGG_BUDGET.json').write_text(json.dumps(out,indent=1)+'\n')
