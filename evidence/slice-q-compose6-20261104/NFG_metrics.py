"""Exact per-attempt release/audit fields; failed drafts are retained."""
from pathlib import Path
import json,hashlib,collections
E=Path(__file__).resolve().parent
rows=[]
for f in sorted(E.glob('NFG_*/receipt.json')):
 r=json.loads(f.read_text())
 if r.get('kind') not in ['lean','kani','extract']:continue
 a=r['attempt'];out=dict(attempt=a,kind=r['kind'],target=r.get('target',r.get('module')),exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=r['swaps'],source_revision=r['source_revision'],source_tree_dirty=r.get('source_tree_dirty'),source_hashes=r['source_hashes'],print_axioms=r.get('print_axioms','N/A'),limits=r['limits'],receipt_sha256=hashlib.sha256(f.read_bytes()).hexdigest())
 assert int(out['swap'])==0
 assert out['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 out['disposition']='retained attempt; only NFG_PACKETS/NFG_CERTIFICATES admit root evidence'
 if a in ['NFG_K008','NFG_K013','NFG_K018','NFG_K045']:out['disposition']='TIMEOUT; OPEN, never rerun unchanged'
 if a=='NFG_L028':out['disposition']='EXCLUDED nonstandard native-decide axiom; superseded L036'
 if a in ['NFG_K007','NFG_K023','NFG_K030']:out['disposition']='EXCLUDED setup/harness/copy-stub failure'
 if r['exit_status'] and r['kind']=='lean':out['disposition']='EXCLUDED failed draft'
 rows.append(out)
counts=dict(collections.Counter(x['kind'] for x in rows));assert counts=={'extract':4,'kani':45,'lean':90},counts
lines=[json.loads(x) for x in (E/'NFG_ATTEMPTS.jsonl').read_text().splitlines()]
assert {x['attempt'] for x in rows}=={x['attempt'] for x in lines} and len(lines)==len(rows),'attempt log mismatch'
(E/'NFG_RUNS.json').write_text(json.dumps(dict(counts=counts,limits=dict(kani=110,lean=90,extract=10),peak_rss_kib=max(int(x['peak_rss_kib']) for x in rows),swaps=0,attempts=rows),indent=1)+'\n')
print(json.dumps(dict(counts=counts,attempts=len(rows),peak_rss_kib=max(int(x['peak_rss_kib']) for x in rows))))
