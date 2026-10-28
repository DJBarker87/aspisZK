from pathlib import Path
import json
E=Path(__file__).resolve().parent
for kind in ['K','L']:
 rows=[]
 for p in sorted(E.glob('NBZ_'+kind+'*/receipt.json')):
  r=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
  status='PASS' if r['exit_status']==0 else 'TIMEOUT' if 'timed out' in log or r['exit_status']==124 else 'ASSERTION_FAIL' if 'Failed Checks:' in log else 'EXCLUDED'
  rows.append(dict(attempt=r['attempt'],status=status,wall=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps']))
 print(kind,json.dumps(rows))
