from pathlib import Path
import json,tarfile,hashlib
from run import H
R=H/'resume16';rows=[]
for p in sorted(R.glob('K*/receipt/receipt.json')):
 x=json.loads(p.read_text());d=p.parent.parent;out=(p.parent/'stdout.log').read_text();reservation=json.loads((d/'reservation.json').read_text());barrier=json.loads((d/'barrier.json').read_text());assert reservation['allowed'] is True and barrier['allowed'] is True
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},x['limits']
 inputs=json.loads((R/(d.name+'-inputs.json')).read_text())
 rows.append(dict(run=d.name,harness=inputs['harness'],status='PASS' if 'VERIFICATION:- SUCCESSFUL'in out else 'EXPECTED/UNEXPECTED FAIL' if 'VERIFICATION:- FAILED'in out else 'TIMEOUT' if x['exit_status']==124 else 'COMPILE/ENV FAILURE',receipt=str(p.relative_to(R)),exit=x['exit_status'],wall=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],cgroup_peak_bytes=x['cgroup_memory_peak_bytes'],swaps=x['swaps'],source_revision=x['source_revision'],source_hashes=inputs.get('source_hashes',{}),print_axioms=x['print_axioms']))
assert len(rows)<=40
(R/'run-index.json').write_text(json.dumps(rows,indent=2)+'\n')
with tarfile.open(H/'resume16-receipts.tar.gz','w:gz') as t:
 for p in R.rglob('*'):
  if p.is_file() and (p.suffix in ['.json','.log'] or p.name=='revision'):t.add(p,arcname=str(p.relative_to(R)))
print(json.dumps(dict(charged=len(rows),statuses={s:sum(r['status']==s for r in rows)for s in set(r['status']for r in rows)})))
