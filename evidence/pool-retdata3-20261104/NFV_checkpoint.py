from pathlib import Path
import json
E=Path(__file__).resolve().parent
def checkpoint():
 rows=[json.loads(l) for l in (E/'NFV_ATTEMPTS.jsonl').read_text().splitlines()]
 used={k:sum(r['kind']==k for r in rows) for k in ['kani','lean','extract']}
 (E/'NFV_BUDGET.json').write_text(json.dumps(dict(limits=dict(kani=80,lean=50,extract=1),used=used),indent=1)+'\n')
