from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(E.glob('NCG_K[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text();name=r['attempt'];h=r['command'][r['command'].index('--harness')+1]
 if 'could not compile' in log:status='COMPILE_FAILURE'
 elif 'timed out' in log or r['exit_status']==124:status='TIMEOUT'
 elif r['exit_status']==0:status='PASS_REQUIRES_CONTROL_AND_DOMAIN_AUDIT'
 elif 'VERIFICATION:- FAILED' in log:status='FAIL_REQUIRES_EXPECTED_PROPERTY_AUDIT'
 else:status='OTHER_FAILURE'
 rows.append(dict(attempt=name,harness=h,status=status,exit=r['exit_status'],wall=r['wall_seconds'],rss=r['peak_rss_kib'],swap=r['swaps'],negative=('negative' in h or any(x in h for x in ['_wrong','_unimplied','_inverted']))))
(E/'NCG_RUNS.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(dict(kani_invocations=len(rows),status_counts={s:sum(r['status']==s for r in rows) for s in sorted({r['status'] for r in rows})},lean_invocations=len(list(E.glob('NCG_L[0-9][0-9][0-9]/receipt.json')))),indent=2))
