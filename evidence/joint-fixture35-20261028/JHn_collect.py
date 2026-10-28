from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[]
for f in sorted(P.glob('JHn35_[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(f.read_text());r['evidence']=str(f.relative_to(R));r['errors']=[x for x in f.with_name('stdout.log').read_text().splitlines() if 'error' in x.lower() or 'excessive memory' in x.lower()]
 rows.append(r)
(P/'JHn_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
summary=dict(attempts=len(rows),passed=sum(r['exit_status']==0 for r in rows),failed=sum(r['exit_status']!=0 for r in rows),wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max((int(r['peak_rss_kib']) for r in rows),default=0),swaps=sum(int(r['swaps']) for r in rows))
(P/'JHn_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))
