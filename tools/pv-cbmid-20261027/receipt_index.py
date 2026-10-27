"""Render a compact index of retained run receipts; no theorem claims added."""
from pathlib import Path
import json
root=Path(__file__).resolve().parents[2]; out=root/'evidence/pv-cbmid-20261027'
rows=['# Run receipt index','','Every row links to the full receipt, including exact command, source revision, limits, and retained logs. Admission refusals are uncharged and retained separately. Timeout RSS is subject to the caveat in its receipt.','','| receipt | target | exit | wall | peak RSS KiB | swap | revision | axioms |','|---|---|---:|---|---|---|---|---|']
paths=sorted(out.glob('[0-9][0-9][0-9][0-9][0-9].json'))+sorted(out.glob('*/receipt.json'))
for p in paths:
 r=json.loads(p.read_text()); target=r.get('module',r.get('target',[]))
 if isinstance(target,list): target=' '.join(target)
 target=str(target).replace('|','\\|')
 axioms=r.get('axioms',r.get('print_axioms','not recorded'))
 if isinstance(axioms,list):
  axioms='; '.join(axioms)
 axioms=str(axioms).replace('|','\\|')
 rel=p.relative_to(out)
 rows.append(f"| [{rel}]({rel}) | `{target}` | {r.get('exit','?')} | {r.get('wall','?')} | {r.get('peak_rss_kib','?')} | {r.get('swap','?')} | {r.get('source_revision','?')} | {axioms} |")
(out/'RECEIPTS.md').write_text('\n'.join(rows)+'\n')
print(len(paths),'receipts indexed')
