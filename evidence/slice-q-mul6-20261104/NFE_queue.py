from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent
for i,m in enumerate(json.loads((E/'NFE_BUILD_ORDER.json').read_text()),1):
 a=f'NFE_L{i:03}'
 if (E/a/'receipt.json').exists():
  assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0;continue
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NFE_run.py'),a,'lean',m],stdout=f,stderr=subprocess.STDOUT)
 print(a,m,r.returncode,flush=True)
 if r.returncode:break
