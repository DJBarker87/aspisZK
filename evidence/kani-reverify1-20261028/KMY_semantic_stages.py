"""Run the fourteen disjoint scalar append stages, one admitted scope at a time."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for i in range(50,64):
 a=f'KMY_K{i:03}'
 if json.loads((E/(a+'.json')).read_text()).get('deferred') or (E/a/'receipt.json').exists():continue
 used=sum(json.loads(p.read_text())['kind']=='kani' for p in E.glob('KMY_*/receipt.json'))
 assert used<60,used
 subprocess.run([sys.executable,str(E/'KMY_host.py'),a],check=True)
 c=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 if c['exit_status']!=0:
  print('STOP stage',a,'exit',c['exit_status'],'TIMEOUT' if 'CBMC timed out' in log else 'inspect failure FIRST',flush=True)
  break
