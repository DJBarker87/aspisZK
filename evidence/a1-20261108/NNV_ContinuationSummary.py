"""One-line summaries of NNV continuation scopes; no build or host mutation."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent
out=[]
for p in sorted(E.glob('NNV_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text())
 if int(r['attempt'][-3:])<51:continue
 out.append({k:r[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']})
(E/'NNV_CONTINUATION_SUMMARIES.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in out))
print(json.dumps({'continuation_scopes':len(out),'passes':sum(r['exit_status']==0 for r in out)}))
