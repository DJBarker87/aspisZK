from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for item in [dict(attempt=f'NIX_K{i:03}',negative=i%2==0) for i in [73,74]]:
 a=item['attempt']
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():print(a,'NO RECEIPT STOP',flush=True);break
 x=json.loads(p.read_text());log=(E/a/'stdout.log').read_text();print(a,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status'] in [124,137] or 'timed out' in log.lower() or 'error: could not compile' in log or 'graph_matches_frozen' in log:print('STOP shape/input failure; isolate before continuation',flush=True);break
 if not item['negative'] and 'VERIFICATION:- SUCCESSFUL' not in log:print('STOP positive did not pass',flush=True);break
 if item['negative'] and ('VERIFICATION:- FAILED' not in log or 'unwinding failures' in log):print('STOP control did not fail semantically',flush=True);break
