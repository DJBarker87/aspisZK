from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
modules=['CellCanon','TensorOffsets','Reverse','TensorFrame','TensorCellTotal','TensorInnerTotal','TensorOuterStep']
for n,m in enumerate(modules,23):
 a=f'NHI_L{n:03d}';p=E/(a+'-queue.log')
 with p.open('w') as f:r=subprocess.run(['python3',str(E/'NHI_run.py'),a,'lean','NHI_'+m],stdout=f,stderr=subprocess.STDOUT)
 print(a,m,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
