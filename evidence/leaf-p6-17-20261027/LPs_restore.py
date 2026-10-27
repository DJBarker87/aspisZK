from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
inventory=json.loads((E/'LPs_DEPENDENCIES_LPq_SelectedDomain.json').read_text())
for i,x in enumerate(inventory['missing'],1):
 a=f'LPs_L{i:03}'
 if (E/a/'receipt.json').exists():
  assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
  continue
 print(a,x['module'],flush=True)
 r=subprocess.run([sys.executable,str(E/'LPs_build.py'),a,x['source'],x['module']])
 if r.returncode:sys.exit(r.returncode)
 assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
