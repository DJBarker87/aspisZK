from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
while not (E/'NGW_L026/receipt.json').exists():time.sleep(2)
assert json.loads((E/'NGW_L026/receipt.json').read_text())['exit_status']==0
jobs=[('NGW_L024','lean','NGW_PointValue'),('NGW_L027','lean','NGW_CellPacket'),('NGW_L028','lean','NGW_COMBINED_IMPORT'),('NGW_L029','lean','NGW_Driver'),('NGW_L030','lean','NGW_ProofDriver'),('NGW_L031','linkaudit','NGW_Driver'),('NGW_L032','linkaudit','NGW_ProofDriver'),('NGW_L033','auditbin','proof0'),('NGW_L034','auditbin','fixtures'),('NGW_L035','auditbin','scan')]
for a,k,n in jobs:
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,k,n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
