"""One serial audit scope per new focused closure group; no headline replay."""
from NMT_audit import audit,E
import json
roots=json.loads((E/'NMT_AUDIT_ROOTS.json').read_text())['groups']
summary=[]
for i in range(2,len(roots)):
 rows=[json.loads(l)for l in (E/'NMT_ATTEMPTS.jsonl').read_text().splitlines()]
 assert not any(r.get('kind')=='audit'and r.get('module')=='proof'+str(i)for r in rows),'Recover existing audit, never resubmit'
 n=max(int(r['attempt'][5:])for r in rows if r.get('attempt','').startswith('NMT_L')and' all'not in r['attempt']and'exit_status'in r)+1
 assert n<=310
 rc,child=audit(f'NMT_L{n:03}','proof'+str(i))
 assert rc['exit_status']==0 and child['exit_status']==0
 assert all(x['equal']for x in child['results'])
 summary.append(dict(attempt=rc['attempt'],mode='proof'+str(i),roots=len(roots[i]),wall_seconds=child['wall_seconds'],peak_rss_kib=child['peak_rss_kib'],swaps=child['swaps'],collector_equal=True,standard_only=True))
 (E/'NMT_RESUME_AUDIT.json').write_text(json.dumps(dict(groups=summary,own_roots=sum(x['roots']for x in summary),collector_equal=True,standard_only=True,scope='own newly printed theorem roots only; no headline/all-roots replay',controls='unchanged raw driver, historical planted/mutation controls NMT_L057 reused'),indent=1)+'\n')
