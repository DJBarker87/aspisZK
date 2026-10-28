from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for i,j in enumerate(json.loads((E/'NCP_LEAN_PLAN.json').read_text()),1):
 a=f'NCP_L{i:03}'
 if (E/a/'receipt.json').exists():
  assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
  continue
 r=subprocess.run(['python3',str(E/'NCP_build.py'),a,j['source'],j['module']],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(a,j['module'],r.returncode,r.stdout[-3500:],flush=True)
 if r.returncode:break
