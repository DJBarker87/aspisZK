"""Persist threshold handoff before another proof launch; no proof/tool mutation."""
from pathlib import Path
import json,collections,hashlib,datetime
E=Path(__file__).resolve().parent
def checkpoint(force=False):
 entries=[json.loads(l) for l in (E/'NFR_ATTEMPTS.jsonl').read_text().splitlines()]
 counts=collections.Counter(x['kind'] for x in entries)
 used=dict(kani=counts['kani'],lean=sum(v for k,v in counts.items() if k not in ['kani','extract']),extract=counts['extract'])
 remaining={k:b-used[k] for k,b in dict(kani=70,lean=60,extract=2).items()}
 if not force and sum(remaining.values())>=15:return
 budget=dict(used=used,remaining=remaining,attempts=len(entries),last_attempt=entries[-1]['attempt'],ledger_sha256=hashlib.sha256((E/'NFR_ATTEMPTS.jsonl').read_bytes()).hexdigest())
 for n in ['NFR_HANDOFF.md','NFR_REMAINING.md','NFR_CONE_DELTA.md']:
  p=E/n;s=p.read_text().split('\n<!-- budget checkpoint -->')[0]
  p.write_text(s+'\n<!-- budget checkpoint -->\nBudget checkpoint: '+json.dumps(budget,sort_keys=True)+'\n')
 for n in ['NFR_AUDIT.json','NFR_INHERITED_INCOHERENCE.json']:
  p=E/n;d=json.loads(p.read_text());d['budget_checkpoint']=budget;p.write_text(json.dumps(d,indent=1)+'\n')
 (E/'NFR_BUDGET.json').write_text(json.dumps(budget,indent=1)+'\n')
if __name__=='__main__':checkpoint(True)
