from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for a in json.loads((E/'NIX_PAIR_PLAN.json').read_text()):
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 if not p.exists():print(a,'NO RECEIPT STOP',flush=True);break
 print(a,r.returncode,json.loads(p.read_text())['wall_seconds'],flush=True)
 log=(E/a/'stdout.log').read_text()
 if 'source-check' in log or not (E/(a+'_PAIR.json')).exists():print('STOP validation/tool failure',flush=True);break
 pair=json.loads((E/(a+'_PAIR.json')).read_text())
 if not pair['children'][1]['expected_verdict']:print('STOP negative-control failure; isolate before continuing',flush=True);break
