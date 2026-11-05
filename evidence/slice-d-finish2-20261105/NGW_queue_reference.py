from pathlib import Path
import subprocess,time,json
E=Path(__file__).resolve().parent
while not (E/'NGW_L020/receipt.json').exists():time.sleep(2)
assert json.loads((E/'NGW_L020/receipt.json').read_text())['exit_status']==0
for a,n in [('NGW_L016','NGW_PointsPacket'),('NGW_L017','NGW_WordExt'),('NGW_L021','NGW_HelperRef/Types'),('NGW_L022','NGW_HelperRef/Funs')]:
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'lean',n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
